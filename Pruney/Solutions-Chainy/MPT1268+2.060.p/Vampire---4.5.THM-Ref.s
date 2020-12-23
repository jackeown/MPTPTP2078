%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 260 expanded)
%              Number of leaves         :   25 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 ( 890 expanded)
%              Number of equality atoms :   28 (  90 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f71,f95,f102,f113,f121,f161,f183,f220,f229,f233,f247,f251,f348,f390])).

fof(f390,plain,
    ( spl4_24
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl4_24
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f388,f232])).

fof(f232,plain,
    ( k1_xboole_0 != sK2
    | spl4_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl4_24
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f388,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_38 ),
    inference(resolution,[],[f381,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f381,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_38 ),
    inference(resolution,[],[f369,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f369,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f368,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f368,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(sK2,X0) )
    | ~ spl4_38 ),
    inference(resolution,[],[f347,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f347,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl4_38
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f348,plain,
    ( spl4_38
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_23
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f342,f249,f227,f123,f100,f69,f65,f346])).

fof(f65,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f69,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f100,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f123,plain,
    ( spl4_10
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f227,plain,
    ( spl4_23
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f249,plain,
    ( spl4_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f342,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_23
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f341,f221])).

fof(f221,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f341,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_23
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f335,f101])).

fof(f101,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f335,plain,
    ( ~ r1_tarski(sK2,sK1)
    | r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_26 ),
    inference(resolution,[],[f268,f70])).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(sK2,k1_tops_1(sK0,X0)) )
    | ~ spl4_2
    | ~ spl4_23
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f267,f228])).

fof(f228,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK2,sK0)
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(sK2,k1_tops_1(sK0,X0)) )
    | ~ spl4_2
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f256,f66])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK2,sK0)
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(sK2,k1_tops_1(sK0,X0)) )
    | ~ spl4_26 ),
    inference(resolution,[],[f250,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f249])).

fof(f251,plain,
    ( spl4_26
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f223,f123,f69,f65,f249])).

fof(f223,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f34,f222])).

fof(f222,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f83,f221])).

fof(f83,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f73,f66])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f247,plain,
    ( spl4_5
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f222,f123,f69,f65,f97])).

fof(f97,plain,
    ( spl4_5
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f233,plain,
    ( ~ spl4_24
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f225,f123,f69,f65,f231])).

fof(f225,plain,
    ( k1_xboole_0 != sK2
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f37,f222])).

fof(f37,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f229,plain,
    ( spl4_23
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f224,f123,f69,f65,f227])).

fof(f224,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f36,f222])).

fof(f36,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f220,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | spl4_10
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f218,f124])).

fof(f124,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f218,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_9
    | spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f217,f112])).

fof(f112,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_7
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f217,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_9
    | spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f216,f120])).

fof(f120,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_9
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f216,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_10
    | ~ spl4_22 ),
    inference(resolution,[],[f210,f182])).

fof(f182,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_22
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f210,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | ~ v3_pre_topc(X2,sK0)
        | k1_xboole_0 = X2 )
    | ~ spl4_2
    | ~ spl4_3
    | spl4_10 ),
    inference(subsumption_resolution,[],[f38,f209])).

fof(f209,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_10 ),
    inference(subsumption_resolution,[],[f84,f124])).

fof(f84,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f74,f66])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f183,plain,
    ( spl4_22
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f174,f159,f181])).

fof(f159,plain,
    ( spl4_17
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f174,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(resolution,[],[f160,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f160,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( spl4_17
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f157,f119,f93,f159])).

fof(f93,plain,
    ( spl4_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f157,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(resolution,[],[f128,f94])).

fof(f94,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f120,f51])).

fof(f121,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f89,f69,f65,f119])).

fof(f89,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f78,f66])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f113,plain,
    ( spl4_7
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f86,f69,f65,f61,f111])).

fof(f61,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f86,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f85,f62])).

fof(f62,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f85,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f75,f66])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f102,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f35,f100,f97])).

fof(f35,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f80,f69,f93])).

fof(f80,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f39,f69])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f65])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f40,f61])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (17183)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (17190)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (17196)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (17183)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (17198)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (17191)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (17199)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f391,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f63,f67,f71,f95,f102,f113,f121,f161,f183,f220,f229,f233,f247,f251,f348,f390])).
% 0.20/0.48  fof(f390,plain,(
% 0.20/0.48    spl4_24 | ~spl4_38),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f389])).
% 0.20/0.48  fof(f389,plain,(
% 0.20/0.48    $false | (spl4_24 | ~spl4_38)),
% 0.20/0.48    inference(subsumption_resolution,[],[f388,f232])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    k1_xboole_0 != sK2 | spl4_24),
% 0.20/0.48    inference(avatar_component_clause,[],[f231])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    spl4_24 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.48  fof(f388,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl4_38),
% 0.20/0.48    inference(resolution,[],[f381,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.48  fof(f381,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl4_38),
% 0.20/0.48    inference(resolution,[],[f369,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.48  fof(f369,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl4_38),
% 0.20/0.48    inference(subsumption_resolution,[],[f368,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f368,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(sK2,X0)) ) | ~spl4_38),
% 0.20/0.48    inference(resolution,[],[f347,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.48  fof(f347,plain,(
% 0.20/0.48    r1_tarski(sK2,k1_xboole_0) | ~spl4_38),
% 0.20/0.48    inference(avatar_component_clause,[],[f346])).
% 0.20/0.48  fof(f346,plain,(
% 0.20/0.48    spl4_38 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.48  fof(f348,plain,(
% 0.20/0.48    spl4_38 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_23 | ~spl4_26),
% 0.20/0.48    inference(avatar_split_clause,[],[f342,f249,f227,f123,f100,f69,f65,f346])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl4_2 <=> l1_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl4_6 <=> r1_tarski(sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl4_10 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    spl4_23 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.48  fof(f249,plain,(
% 0.20/0.48    spl4_26 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.48  fof(f342,plain,(
% 0.20/0.48    r1_tarski(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_23 | ~spl4_26)),
% 0.20/0.48    inference(forward_demodulation,[],[f341,f221])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f341,plain,(
% 0.20/0.48    r1_tarski(sK2,k1_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_23 | ~spl4_26)),
% 0.20/0.48    inference(subsumption_resolution,[],[f335,f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | ~spl4_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f100])).
% 0.20/0.48  fof(f335,plain,(
% 0.20/0.48    ~r1_tarski(sK2,sK1) | r1_tarski(sK2,k1_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_23 | ~spl4_26)),
% 0.20/0.48    inference(resolution,[],[f268,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) ) | (~spl4_2 | ~spl4_23 | ~spl4_26)),
% 0.20/0.48    inference(subsumption_resolution,[],[f267,f228])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    v3_pre_topc(sK2,sK0) | ~spl4_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f227])).
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) ) | (~spl4_2 | ~spl4_26)),
% 0.20/0.48    inference(subsumption_resolution,[],[f256,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    l1_pre_topc(sK0) | ~spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f256,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) ) | ~spl4_26),
% 0.20/0.48    inference(resolution,[],[f250,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f249])).
% 0.20/0.48  fof(f251,plain,(
% 0.20/0.48    spl4_26 | ~spl4_2 | ~spl4_3 | ~spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f223,f123,f69,f65,f249])).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_3 | ~spl4_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f34,f222])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    v2_tops_1(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f83,f221])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | (~spl4_2 | ~spl4_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f73,f66])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f70,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f14])).
% 0.20/0.48  fof(f14,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.48  fof(f247,plain,(
% 0.20/0.48    spl4_5 | ~spl4_2 | ~spl4_3 | ~spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f222,f123,f69,f65,f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl4_5 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    ~spl4_24 | ~spl4_2 | ~spl4_3 | ~spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f225,f123,f69,f65,f231])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    k1_xboole_0 != sK2 | (~spl4_2 | ~spl4_3 | ~spl4_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f37,f222])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    spl4_23 | ~spl4_2 | ~spl4_3 | ~spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f224,f123,f69,f65,f227])).
% 0.20/0.48  fof(f224,plain,(
% 0.20/0.48    v3_pre_topc(sK2,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f36,f222])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    ~spl4_2 | ~spl4_3 | ~spl4_7 | ~spl4_9 | spl4_10 | ~spl4_22),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f219])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    $false | (~spl4_2 | ~spl4_3 | ~spl4_7 | ~spl4_9 | spl4_10 | ~spl4_22)),
% 0.20/0.48    inference(subsumption_resolution,[],[f218,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl4_2 | ~spl4_3 | ~spl4_7 | ~spl4_9 | spl4_10 | ~spl4_22)),
% 0.20/0.48    inference(subsumption_resolution,[],[f217,f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl4_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    spl4_7 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl4_2 | ~spl4_3 | ~spl4_9 | spl4_10 | ~spl4_22)),
% 0.20/0.48    inference(subsumption_resolution,[],[f216,f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl4_9 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl4_2 | ~spl4_3 | spl4_10 | ~spl4_22)),
% 0.20/0.48    inference(resolution,[],[f210,f182])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_22),
% 0.20/0.48    inference(avatar_component_clause,[],[f181])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    spl4_22 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2) ) | (~spl4_2 | ~spl4_3 | spl4_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f38,f209])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    ~v2_tops_1(sK1,sK0) | (~spl4_2 | ~spl4_3 | spl4_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f124])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0) | (~spl4_2 | ~spl4_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f74,f66])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f70,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    spl4_22 | ~spl4_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f174,f159,f181])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    spl4_17 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_17),
% 0.20/0.48    inference(resolution,[],[f160,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl4_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f159])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl4_17 | ~spl4_4 | ~spl4_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f157,f119,f93,f159])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl4_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl4_4 | ~spl4_9)),
% 0.20/0.48    inference(resolution,[],[f128,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f93])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl4_9),
% 0.20/0.48    inference(resolution,[],[f120,f51])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl4_9 | ~spl4_2 | ~spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f89,f69,f65,f119])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl4_2 | ~spl4_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f78,f66])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f70,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    spl4_7 | ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f86,f69,f65,f61,f111])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl4_1 <=> v2_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f85,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    v2_pre_topc(sK0) | ~spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f61])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_2 | ~spl4_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f75,f66])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f70,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ~spl4_5 | spl4_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f100,f97])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl4_4 | ~spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f80,f69,f93])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f70,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f69])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f65])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f61])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17183)------------------------------
% 0.20/0.48  % (17183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17183)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17183)Memory used [KB]: 6396
% 0.20/0.48  % (17183)Time elapsed: 0.060 s
% 0.20/0.48  % (17183)------------------------------
% 0.20/0.48  % (17183)------------------------------
% 0.20/0.49  % (17180)Success in time 0.127 s
%------------------------------------------------------------------------------
