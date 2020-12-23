%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 289 expanded)
%              Number of leaves         :   31 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  481 (1034 expanded)
%              Number of equality atoms :   45 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f71,f76,f81,f89,f94,f99,f143,f147,f166,f192,f234,f264,f280,f286,f314,f325,f349])).

fof(f349,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f347,f93])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f347,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_1
    | spl3_4
    | ~ spl3_8
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f346,f88])).

fof(f88,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f346,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | spl3_4
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f345,f49])).

fof(f49,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f345,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_4
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f336,f64])).

fof(f64,plain,
    ( ~ v1_tops_1(sK2,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_4
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f336,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_33 ),
    inference(trivial_inequality_removal,[],[f335])).

fof(f335,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_33 ),
    inference(superposition,[],[f36,f299])).

fof(f299,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl3_33
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f325,plain,
    ( ~ spl3_30
    | spl3_33
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl3_30
    | spl3_33
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f323,f300])).

fof(f300,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK2)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f298])).

fof(f323,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_30
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f319,f279])).

% (10242)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f279,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl3_30
  <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f319,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_36 ),
    inference(resolution,[],[f313,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f313,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),k2_struct_0(sK0))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl3_36
  <=> r1_tarski(k2_pre_topc(sK0,sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f314,plain,
    ( spl3_36
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f287,f284,f91,f311])).

fof(f284,plain,
    ( spl3_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f287,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),k2_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(resolution,[],[f285,f93])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f284])).

fof(f286,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f281,f222,f189,f86,f47,f284])).

fof(f189,plain,
    ( spl3_23
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f222,plain,
    ( spl3_25
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) )
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f200,f223])).

fof(f223,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) )
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f199,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0))
        | ~ r1_tarski(X0,k2_struct_0(sK0)) )
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f198,f88])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0))
        | ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f197,f88])).

fof(f197,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0))
        | ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f193,f49])).

fof(f193,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0))
        | ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_23 ),
    inference(superposition,[],[f37,f191])).

fof(f191,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f189])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
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
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f280,plain,
    ( spl3_30
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f271,f262,f91,f57,f277])).

fof(f57,plain,
    ( spl3_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f262,plain,
    ( spl3_29
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

% (10259)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f271,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f268,f93])).

fof(f268,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(resolution,[],[f263,f59])).

fof(f59,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f263,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f262])).

fof(f264,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f181,f163,f96,f86,f47,f262])).

fof(f96,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f163,plain,
    ( spl3_21
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f181,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(sK1,X1) )
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f180,f98])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f180,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(sK1,X1) )
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f179,f88])).

fof(f179,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f178,f88])).

fof(f178,plain,
    ( ! [X1] :
        ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(sK1,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f171,f49])).

fof(f171,plain,
    ( ! [X1] :
        ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1))
        | ~ r1_tarski(sK1,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_21 ),
    inference(superposition,[],[f37,f165])).

fof(f165,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f234,plain,(
    spl3_25 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl3_25 ),
    inference(subsumption_resolution,[],[f231,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f231,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl3_25 ),
    inference(resolution,[],[f224,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f224,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f192,plain,
    ( spl3_23
    | ~ spl3_10
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f187,f163,f141,f96,f189])).

fof(f141,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f187,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl3_10
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f158,f165])).

fof(f158,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(resolution,[],[f142,f98])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f166,plain,
    ( spl3_21
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f161,f145,f96,f52,f163])).

fof(f52,plain,
    ( spl3_2
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f145,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f161,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f160,f98])).

fof(f160,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(resolution,[],[f146,f54])).

fof(f54,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f147,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f130,f86,f47,f145])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f116,f88])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f35,f49])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f143,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f119,f86,f47,f141])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f118,f88])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f38,f49])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f99,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f84,f73,f68,f96])).

fof(f68,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f73,plain,
    ( spl3_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f70,f82])).

fof(f82,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f33,f75])).

fof(f75,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f94,plain,
    ( spl3_9
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f83,f78,f73,f91])).

fof(f78,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f80,f82])).

fof(f80,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f89,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f82,f73,f86])).

fof(f81,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f78])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v1_tops_1(sK2,sK0)
    & r1_tarski(sK1,sK2)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(X2,X0)
                & r1_tarski(X1,X2)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(X2,sK0)
              & r1_tarski(X1,X2)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(X2,sK0)
            & r1_tarski(X1,X2)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(X2,sK0)
          & r1_tarski(sK1,X2)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(X2,sK0)
        & r1_tarski(sK1,X2)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(sK2,sK0)
      & r1_tarski(sK1,sK2)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(X2,X0)
              & r1_tarski(X1,X2)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(X2,X0)
              & r1_tarski(X1,X2)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

fof(f76,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f66,f47,f73])).

fof(f66,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f34,f49])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    ~ v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f30,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f47])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:12:51 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.50  % (10238)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (10244)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (10248)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (10262)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (10240)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (10255)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (10249)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (10254)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (10243)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (10257)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (10251)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (10264)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (10245)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (10240)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (10243)Refutation not found, incomplete strategy% (10243)------------------------------
% 0.22/0.52  % (10243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10243)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10243)Memory used [KB]: 6140
% 0.22/0.52  % (10243)Time elapsed: 0.104 s
% 0.22/0.52  % (10243)------------------------------
% 0.22/0.52  % (10243)------------------------------
% 0.22/0.52  % (10247)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (10253)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (10245)Refutation not found, incomplete strategy% (10245)------------------------------
% 0.22/0.52  % (10245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10245)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10245)Memory used [KB]: 1663
% 0.22/0.52  % (10245)Time elapsed: 0.068 s
% 0.22/0.52  % (10245)------------------------------
% 0.22/0.52  % (10245)------------------------------
% 0.22/0.52  % (10239)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (10252)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (10260)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (10256)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (10241)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (10261)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (10246)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (10263)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f350,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f71,f76,f81,f89,f94,f99,f143,f147,f166,f192,f234,f264,f280,f286,f314,f325,f349])).
% 0.22/0.53  fof(f349,plain,(
% 0.22/0.53    ~spl3_1 | spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_33),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f348])).
% 0.22/0.53  fof(f348,plain,(
% 0.22/0.53    $false | (~spl3_1 | spl3_4 | ~spl3_8 | ~spl3_9 | ~spl3_33)),
% 0.22/0.53    inference(subsumption_resolution,[],[f347,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f347,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_1 | spl3_4 | ~spl3_8 | ~spl3_33)),
% 0.22/0.53    inference(forward_demodulation,[],[f346,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl3_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f346,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | spl3_4 | ~spl3_33)),
% 0.22/0.53    inference(subsumption_resolution,[],[f345,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    l1_pre_topc(sK0) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl3_1 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f345,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_4 | ~spl3_33)),
% 0.22/0.53    inference(subsumption_resolution,[],[f336,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ~v1_tops_1(sK2,sK0) | spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    spl3_4 <=> v1_tops_1(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f336,plain,(
% 0.22/0.53    v1_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_33),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f335])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_33),
% 0.22/0.53    inference(superposition,[],[f36,f299])).
% 0.22/0.53  fof(f299,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | ~spl3_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f298])).
% 0.22/0.53  fof(f298,plain,(
% 0.22/0.53    spl3_33 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.53  fof(f325,plain,(
% 0.22/0.53    ~spl3_30 | spl3_33 | ~spl3_36),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f324])).
% 0.22/0.53  fof(f324,plain,(
% 0.22/0.53    $false | (~spl3_30 | spl3_33 | ~spl3_36)),
% 0.22/0.53    inference(subsumption_resolution,[],[f323,f300])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    k2_struct_0(sK0) != k2_pre_topc(sK0,sK2) | spl3_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f298])).
% 0.22/0.53  fof(f323,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | (~spl3_30 | ~spl3_36)),
% 0.22/0.53    inference(subsumption_resolution,[],[f319,f279])).
% 0.22/0.53  % (10242)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2)) | ~spl3_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f277])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    spl3_30 <=> r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.53  fof(f319,plain,(
% 0.22/0.53    ~r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2)) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | ~spl3_36),
% 0.22/0.53    inference(resolution,[],[f313,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f313,plain,(
% 0.22/0.53    r1_tarski(k2_pre_topc(sK0,sK2),k2_struct_0(sK0)) | ~spl3_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f311])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    spl3_36 <=> r1_tarski(k2_pre_topc(sK0,sK2),k2_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    spl3_36 | ~spl3_9 | ~spl3_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f287,f284,f91,f311])).
% 0.22/0.53  fof(f284,plain,(
% 0.22/0.53    spl3_31 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    r1_tarski(k2_pre_topc(sK0,sK2),k2_struct_0(sK0)) | (~spl3_9 | ~spl3_31)),
% 0.22/0.53    inference(resolution,[],[f285,f93])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0))) ) | ~spl3_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f284])).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    spl3_31 | ~spl3_1 | ~spl3_8 | ~spl3_23 | ~spl3_25),
% 0.22/0.53    inference(avatar_split_clause,[],[f281,f222,f189,f86,f47,f284])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    spl3_23 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    spl3_25 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0))) ) | (~spl3_1 | ~spl3_8 | ~spl3_23 | ~spl3_25)),
% 0.22/0.53    inference(subsumption_resolution,[],[f200,f223])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f222])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0))) ) | (~spl3_1 | ~spl3_8 | ~spl3_23)),
% 0.22/0.53    inference(subsumption_resolution,[],[f199,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) | ~r1_tarski(X0,k2_struct_0(sK0))) ) | (~spl3_1 | ~spl3_8 | ~spl3_23)),
% 0.22/0.53    inference(forward_demodulation,[],[f198,f88])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) | ~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_8 | ~spl3_23)),
% 0.22/0.53    inference(forward_demodulation,[],[f197,f88])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) | ~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_23)),
% 0.22/0.53    inference(subsumption_resolution,[],[f193,f49])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) | ~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_23),
% 0.22/0.53    inference(superposition,[],[f37,f191])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl3_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f189])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    spl3_30 | ~spl3_3 | ~spl3_9 | ~spl3_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f271,f262,f91,f57,f277])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl3_3 <=> r1_tarski(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    spl3_29 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) | ~r1_tarski(sK1,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.53  % (10259)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  fof(f271,plain,(
% 0.22/0.53    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2)) | (~spl3_3 | ~spl3_9 | ~spl3_29)),
% 0.22/0.53    inference(subsumption_resolution,[],[f268,f93])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | ~spl3_29)),
% 0.22/0.53    inference(resolution,[],[f263,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_tarski(sK1,X1) | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f262])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    spl3_29 | ~spl3_1 | ~spl3_8 | ~spl3_10 | ~spl3_21),
% 0.22/0.53    inference(avatar_split_clause,[],[f181,f163,f96,f86,f47,f262])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl3_10 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    spl3_21 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) | ~r1_tarski(sK1,X1)) ) | (~spl3_1 | ~spl3_8 | ~spl3_10 | ~spl3_21)),
% 0.22/0.53    inference(subsumption_resolution,[],[f180,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) | ~r1_tarski(sK1,X1)) ) | (~spl3_1 | ~spl3_8 | ~spl3_21)),
% 0.22/0.53    inference(forward_demodulation,[],[f179,f88])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) | ~r1_tarski(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_8 | ~spl3_21)),
% 0.22/0.53    inference(forward_demodulation,[],[f178,f88])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) | ~r1_tarski(sK1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_21)),
% 0.22/0.53    inference(subsumption_resolution,[],[f171,f49])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) | ~r1_tarski(sK1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_21),
% 0.22/0.53    inference(superposition,[],[f37,f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl3_21),
% 0.22/0.53    inference(avatar_component_clause,[],[f163])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    spl3_25),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f233])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    $false | spl3_25),
% 0.22/0.53    inference(subsumption_resolution,[],[f231,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | spl3_25),
% 0.22/0.53    inference(resolution,[],[f224,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f222])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    spl3_23 | ~spl3_10 | ~spl3_17 | ~spl3_21),
% 0.22/0.53    inference(avatar_split_clause,[],[f187,f163,f141,f96,f189])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    spl3_17 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | (~spl3_10 | ~spl3_17 | ~spl3_21)),
% 0.22/0.53    inference(forward_demodulation,[],[f158,f165])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) | (~spl3_10 | ~spl3_17)),
% 0.22/0.53    inference(resolution,[],[f142,f98])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | ~spl3_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f141])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    spl3_21 | ~spl3_2 | ~spl3_10 | ~spl3_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f161,f145,f96,f52,f163])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl3_2 <=> v1_tops_1(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    spl3_18 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_10 | ~spl3_18)),
% 0.22/0.53    inference(subsumption_resolution,[],[f160,f98])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_18)),
% 0.22/0.53    inference(resolution,[],[f146,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    v1_tops_1(sK1,sK0) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f52])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl3_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f145])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl3_18 | ~spl3_1 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f130,f86,f47,f145])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | (~spl3_1 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f116,f88])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f35,f49])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    spl3_17 | ~spl3_1 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f119,f86,f47,f141])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | (~spl3_1 | ~spl3_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f118,f88])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f38,f49])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl3_10 | ~spl3_5 | ~spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f84,f73,f68,f96])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl3_6 <=> l1_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_6)),
% 0.22/0.53    inference(backward_demodulation,[],[f70,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_6),
% 0.22/0.53    inference(resolution,[],[f33,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    l1_struct_0(sK0) | ~spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f73])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f68])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    spl3_9 | ~spl3_6 | ~spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f83,f78,f73,f91])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_6 | ~spl3_7)),
% 0.22/0.53    inference(backward_demodulation,[],[f80,f82])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl3_8 | ~spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f82,f73,f86])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f78])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ((~v1_tops_1(sK2,sK0) & r1_tarski(sK1,sK2) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(X2,X0) & r1_tarski(X1,X2) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(X2,sK0) & r1_tarski(X1,X2) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (~v1_tops_1(X2,sK0) & r1_tarski(X1,X2) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(X2,sK0) & r1_tarski(sK1,X2) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X2] : (~v1_tops_1(X2,sK0) & r1_tarski(sK1,X2) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(sK2,sK0) & r1_tarski(sK1,sK2) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(X2,X0) & r1_tarski(X1,X2) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(X2,X0) & (r1_tarski(X1,X2) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl3_6 | ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f66,f47,f73])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    l1_struct_0(sK0) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f34,f49])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f68])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f62])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ~v1_tops_1(sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f57])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f52])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    v1_tops_1(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f47])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10240)------------------------------
% 0.22/0.53  % (10240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10240)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10240)Memory used [KB]: 6268
% 0.22/0.53  % (10240)Time elapsed: 0.101 s
% 0.22/0.53  % (10240)------------------------------
% 0.22/0.53  % (10240)------------------------------
% 0.22/0.54  % (10244)Refutation not found, incomplete strategy% (10244)------------------------------
% 0.22/0.54  % (10244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10244)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10244)Memory used [KB]: 10874
% 0.22/0.54  % (10244)Time elapsed: 0.104 s
% 0.22/0.54  % (10244)------------------------------
% 0.22/0.54  % (10244)------------------------------
% 0.22/0.54  % (10235)Success in time 0.173 s
%------------------------------------------------------------------------------
