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
% DateTime   : Thu Dec  3 13:15:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 413 expanded)
%              Number of leaves         :   50 ( 184 expanded)
%              Depth                    :   11
%              Number of atoms          :  855 (1873 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f90,f95,f99,f103,f111,f122,f129,f132,f145,f155,f161,f178,f188,f206,f220,f240,f244,f250,f255,f260,f268,f274,f284,f287,f296,f300,f307,f342,f350,f357,f364,f369,f374])).

fof(f374,plain,
    ( ~ spl3_6
    | spl3_18
    | ~ spl3_42
    | ~ spl3_51 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl3_6
    | spl3_18
    | ~ spl3_42
    | ~ spl3_51 ),
    inference(subsumption_resolution,[],[f372,f153])).

fof(f153,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_18
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f372,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_6
    | ~ spl3_42
    | ~ spl3_51 ),
    inference(subsumption_resolution,[],[f371,f94])).

fof(f94,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f371,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_42
    | ~ spl3_51 ),
    inference(resolution,[],[f368,f306])).

fof(f306,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl3_42
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(X0,sK0,sK1) )
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl3_51
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | m1_connsp_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f369,plain,
    ( spl3_51
    | ~ spl3_4
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f365,f362,f83,f367])).

fof(f83,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f362,plain,
    ( spl3_50
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | m1_connsp_2(X0,sK0,sK1) )
    | ~ spl3_4
    | ~ spl3_50 ),
    inference(resolution,[],[f363,f85])).

fof(f85,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f363,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | m1_connsp_2(X1,sK0,X0) )
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f362])).

fof(f364,plain,
    ( spl3_50
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f360,f355,f78,f73,f68,f362])).

fof(f68,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f73,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f355,plain,
    ( spl3_49
  <=> ! [X1,X0,X2] :
        ( m1_connsp_2(X2,X0,X1)
        | ~ r2_hidden(X1,k1_tops_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f360,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f359,f70])).

fof(f70,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f359,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f358,f80])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f358,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | m1_connsp_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_49 ),
    inference(resolution,[],[f356,f75])).

fof(f75,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f356,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ r2_hidden(X1,k1_tops_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | m1_connsp_2(X2,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f355])).

fof(f357,plain,(
    spl3_49 ),
    inference(avatar_split_clause,[],[f53,f355])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f350,plain,
    ( ~ spl3_18
    | ~ spl3_4
    | ~ spl3_6
    | spl3_12
    | ~ spl3_22
    | ~ spl3_39
    | ~ spl3_40
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f348,f340,f281,f277,f176,f119,f92,f83,f152])).

fof(f119,plain,
    ( spl3_12
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f176,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f277,plain,
    ( spl3_39
  <=> r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f281,plain,
    ( spl3_40
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f340,plain,
    ( spl3_48
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f348,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_4
    | ~ spl3_6
    | spl3_12
    | ~ spl3_22
    | ~ spl3_39
    | ~ spl3_40
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f189,f345])).

fof(f345,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl3_6
    | ~ spl3_39
    | ~ spl3_40
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f344,f282])).

fof(f282,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f281])).

fof(f344,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl3_6
    | ~ spl3_39
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f343,f94])).

fof(f343,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl3_39
    | ~ spl3_48 ),
    inference(resolution,[],[f341,f279])).

fof(f279,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f277])).

fof(f341,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f340])).

fof(f189,plain,
    ( ~ m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_4
    | spl3_12
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f48,f182])).

fof(f182,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl3_4
    | spl3_12
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f179,f120])).

fof(f120,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f179,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(resolution,[],[f177,f85])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | v1_xboole_0(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f176])).

fof(f48,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK0,X1)
              | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & ( m1_connsp_2(X2,sK0,X1)
              | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK0,sK1)
            | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & ( m1_connsp_2(X2,sK0,sK1)
            | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK0,sK1)
          | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & ( m1_connsp_2(X2,sK0,sK1)
          | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(sK2,sK0,sK1)
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & ( m1_connsp_2(sK2,sK0,sK1)
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f342,plain,
    ( spl3_48
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f338,f298,f78,f73,f340])).

fof(f298,plain,
    ( spl3_41
  <=> ! [X1,X0,X2] :
        ( m2_connsp_2(X2,X0,X1)
        | ~ r1_tarski(X1,k1_tops_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f337,f80])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl3_2
    | ~ spl3_41 ),
    inference(resolution,[],[f299,f75])).

fof(f299,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tarski(X1,k1_tops_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | m2_connsp_2(X2,X0,X1) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f298])).

fof(f307,plain,
    ( spl3_42
    | ~ spl3_10
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f301,f277,f109,f304])).

fof(f109,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f301,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_10
    | ~ spl3_39 ),
    inference(resolution,[],[f279,f110])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f300,plain,(
    spl3_41 ),
    inference(avatar_split_clause,[],[f55,f298])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f296,plain,
    ( spl3_39
    | ~ spl3_18
    | ~ spl3_34
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f295,f258,f248,f152,f277])).

fof(f248,plain,
    ( spl3_34
  <=> ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | r2_hidden(sK1,k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f258,plain,
    ( spl3_36
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
        | r1_tarski(k2_tarski(sK1,X0),k1_tops_1(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f295,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ spl3_18
    | ~ spl3_34
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f294,f154])).

fof(f154,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f294,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl3_34
    | ~ spl3_36 ),
    inference(resolution,[],[f259,f249])).

fof(f249,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f248])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
        | r1_tarski(k2_tarski(sK1,X0),k1_tops_1(sK0,sK2)) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f258])).

fof(f287,plain,
    ( ~ spl3_11
    | ~ spl3_16
    | spl3_40 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_16
    | spl3_40 ),
    inference(subsumption_resolution,[],[f285,f117])).

fof(f117,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

% (22935)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f115,plain,
    ( spl3_11
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f285,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_16
    | spl3_40 ),
    inference(resolution,[],[f283,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f283,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f281])).

fof(f284,plain,
    ( spl3_39
    | ~ spl3_40
    | ~ spl3_23
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f275,f272,f185,f281,f277])).

fof(f185,plain,
    ( spl3_23
  <=> m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f272,plain,
    ( spl3_38
  <=> ! [X1,X0] :
        ( ~ m2_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X1,k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f275,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ spl3_23
    | ~ spl3_38 ),
    inference(resolution,[],[f273,f187])).

fof(f187,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( ~ m2_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X1,k1_tops_1(sK0,X0)) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f272])).

fof(f274,plain,
    ( spl3_38
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f270,f266,f78,f73,f272])).

fof(f266,plain,
    ( spl3_37
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,k1_tops_1(X0,X2))
        | ~ m2_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ m2_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X1,k1_tops_1(sK0,X0)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f269,f80])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ m2_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | r1_tarski(X1,k1_tops_1(sK0,X0)) )
    | ~ spl3_2
    | ~ spl3_37 ),
    inference(resolution,[],[f267,f75])).

fof(f267,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ m2_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | r1_tarski(X1,k1_tops_1(X0,X2)) )
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f266])).

fof(f268,plain,
    ( spl3_37
    | ~ spl3_26
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f245,f242,f204,f266])).

fof(f204,plain,
    ( spl3_26
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f242,plain,
    ( spl3_33
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,k1_tops_1(X0,X2))
        | ~ m2_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X1,k1_tops_1(X0,X2))
        | ~ m2_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_26
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f243,f205])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_connsp_2(X2,X0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f204])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X1,k1_tops_1(X0,X2))
        | ~ m2_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f242])).

fof(f260,plain,
    ( spl3_36
    | ~ spl3_18
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f256,f253,f152,f258])).

fof(f253,plain,
    ( spl3_35
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
        | r1_tarski(k2_tarski(sK1,X1),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
        | r1_tarski(k2_tarski(sK1,X0),k1_tops_1(sK0,sK2)) )
    | ~ spl3_18
    | ~ spl3_35 ),
    inference(resolution,[],[f254,f154])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
        | r1_tarski(k2_tarski(sK1,X1),k1_tops_1(sK0,X0)) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl3_35
    | ~ spl3_19
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f251,f248,f159,f253])).

fof(f159,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
        | r1_tarski(k2_tarski(sK1,X1),k1_tops_1(sK0,X0)) )
    | ~ spl3_19
    | ~ spl3_34 ),
    inference(resolution,[],[f249,f160])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X2)
        | r1_tarski(k2_tarski(X0,X1),X2) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f159])).

fof(f250,plain,
    ( spl3_34
    | ~ spl3_4
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f246,f238,f83,f248])).

fof(f238,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | r2_hidden(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl3_4
    | ~ spl3_32 ),
    inference(resolution,[],[f239,f85])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X1,k1_tops_1(sK0,X0)) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f238])).

fof(f244,plain,(
    spl3_33 ),
    inference(avatar_split_clause,[],[f54,f242])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f240,plain,
    ( spl3_32
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f236,f218,f78,f73,f68,f238])).

fof(f218,plain,
    ( spl3_29
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X1,k1_tops_1(X0,X2))
        | ~ m1_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k1_tops_1(sK0,X0)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f235,f70])).

% (22950)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f234,f80])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(resolution,[],[f219,f75])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k1_tops_1(X0,X2))
        | v2_struct_0(X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f66,f218])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f206,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f60,f204])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(f188,plain,
    ( spl3_23
    | ~ spl3_4
    | spl3_12
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f183,f176,f148,f119,f83,f185])).

fof(f148,plain,
    ( spl3_17
  <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f183,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl3_4
    | spl3_12
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f150,f182])).

fof(f150,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f178,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f65,f176])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f58,f49])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f161,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f63,f159])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f155,plain,
    ( spl3_17
    | spl3_18 ),
    inference(avatar_split_clause,[],[f47,f152,f148])).

fof(f47,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f145,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f64,f143])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f49])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f132,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | spl3_13 ),
    inference(subsumption_resolution,[],[f130,f80])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_5
    | spl3_13 ),
    inference(resolution,[],[f128,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_5
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f128,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_13
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f129,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f124,f119,f97,f68,f126])).

fof(f97,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f124,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_1
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f123,f70])).

fof(f123,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(resolution,[],[f121,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f121,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f122,plain,
    ( spl3_11
    | spl3_12
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f112,f101,f83,f119,f115])).

fof(f101,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f112,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f102,f85])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f111,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f62,f109])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f57,f101])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f99,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f51,f97])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f95,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f88])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f86,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f43,f73])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f42,f68])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (22949)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (22941)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (22936)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (22937)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (22947)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (22941)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (22943)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (22940)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (22944)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (22938)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (22946)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f375,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f90,f95,f99,f103,f111,f122,f129,f132,f145,f155,f161,f178,f188,f206,f220,f240,f244,f250,f255,f260,f268,f274,f284,f287,f296,f300,f307,f342,f350,f357,f364,f369,f374])).
% 0.20/0.47  fof(f374,plain,(
% 0.20/0.47    ~spl3_6 | spl3_18 | ~spl3_42 | ~spl3_51),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f373])).
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    $false | (~spl3_6 | spl3_18 | ~spl3_42 | ~spl3_51)),
% 0.20/0.47    inference(subsumption_resolution,[],[f372,f153])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    ~m1_connsp_2(sK2,sK0,sK1) | spl3_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f152])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    spl3_18 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.47  fof(f372,plain,(
% 0.20/0.47    m1_connsp_2(sK2,sK0,sK1) | (~spl3_6 | ~spl3_42 | ~spl3_51)),
% 0.20/0.47    inference(subsumption_resolution,[],[f371,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f371,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1) | (~spl3_42 | ~spl3_51)),
% 0.20/0.47    inference(resolution,[],[f368,f306])).
% 0.20/0.47  fof(f306,plain,(
% 0.20/0.47    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl3_42),
% 0.20/0.47    inference(avatar_component_clause,[],[f304])).
% 0.20/0.47  fof(f304,plain,(
% 0.20/0.47    spl3_42 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.47  fof(f368,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1)) ) | ~spl3_51),
% 0.20/0.47    inference(avatar_component_clause,[],[f367])).
% 0.20/0.47  fof(f367,plain,(
% 0.20/0.47    spl3_51 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | m1_connsp_2(X0,sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.47  fof(f369,plain,(
% 0.20/0.47    spl3_51 | ~spl3_4 | ~spl3_50),
% 0.20/0.47    inference(avatar_split_clause,[],[f365,f362,f83,f367])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl3_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f362,plain,(
% 0.20/0.47    spl3_50 <=> ! [X1,X0] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.47  fof(f365,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | m1_connsp_2(X0,sK0,sK1)) ) | (~spl3_4 | ~spl3_50)),
% 0.20/0.47    inference(resolution,[],[f363,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f83])).
% 0.20/0.47  fof(f363,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0)) ) | ~spl3_50),
% 0.20/0.47    inference(avatar_component_clause,[],[f362])).
% 0.20/0.47  fof(f364,plain,(
% 0.20/0.47    spl3_50 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_49),
% 0.20/0.47    inference(avatar_split_clause,[],[f360,f355,f78,f73,f68,f362])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl3_2 <=> v2_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl3_3 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f355,plain,(
% 0.20/0.47    spl3_49 <=> ! [X1,X0,X2] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.47  fof(f360,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_49)),
% 0.20/0.47    inference(subsumption_resolution,[],[f359,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ~v2_struct_0(sK0) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f359,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_49)),
% 0.20/0.47    inference(subsumption_resolution,[],[f358,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f358,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_49)),
% 0.20/0.47    inference(resolution,[],[f356,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    v2_pre_topc(sK0) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f73])).
% 0.20/0.47  fof(f356,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) ) | ~spl3_49),
% 0.20/0.47    inference(avatar_component_clause,[],[f355])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    spl3_49),
% 0.20/0.47    inference(avatar_split_clause,[],[f53,f355])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.47  fof(f350,plain,(
% 0.20/0.47    ~spl3_18 | ~spl3_4 | ~spl3_6 | spl3_12 | ~spl3_22 | ~spl3_39 | ~spl3_40 | ~spl3_48),
% 0.20/0.47    inference(avatar_split_clause,[],[f348,f340,f281,f277,f176,f119,f92,f83,f152])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl3_12 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    spl3_22 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.47  fof(f277,plain,(
% 0.20/0.47    spl3_39 <=> r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.47  fof(f281,plain,(
% 0.20/0.47    spl3_40 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.47  fof(f340,plain,(
% 0.20/0.47    spl3_48 <=> ! [X1,X0] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.47  fof(f348,plain,(
% 0.20/0.47    ~m1_connsp_2(sK2,sK0,sK1) | (~spl3_4 | ~spl3_6 | spl3_12 | ~spl3_22 | ~spl3_39 | ~spl3_40 | ~spl3_48)),
% 0.20/0.47    inference(subsumption_resolution,[],[f189,f345])).
% 0.20/0.47  fof(f345,plain,(
% 0.20/0.47    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl3_6 | ~spl3_39 | ~spl3_40 | ~spl3_48)),
% 0.20/0.47    inference(subsumption_resolution,[],[f344,f282])).
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_40),
% 0.20/0.47    inference(avatar_component_clause,[],[f281])).
% 0.20/0.47  fof(f344,plain,(
% 0.20/0.47    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl3_6 | ~spl3_39 | ~spl3_48)),
% 0.20/0.47    inference(subsumption_resolution,[],[f343,f94])).
% 0.20/0.47  fof(f343,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl3_39 | ~spl3_48)),
% 0.20/0.47    inference(resolution,[],[f341,f279])).
% 0.20/0.47  fof(f279,plain,(
% 0.20/0.47    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~spl3_39),
% 0.20/0.47    inference(avatar_component_clause,[],[f277])).
% 0.20/0.47  fof(f341,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0)) ) | ~spl3_48),
% 0.20/0.47    inference(avatar_component_clause,[],[f340])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    ~m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~m1_connsp_2(sK2,sK0,sK1) | (~spl3_4 | spl3_12 | ~spl3_22)),
% 0.20/0.47    inference(forward_demodulation,[],[f48,f182])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | (~spl3_4 | spl3_12 | ~spl3_22)),
% 0.20/0.47    inference(subsumption_resolution,[],[f179,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f119])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0)) | (~spl3_4 | ~spl3_22)),
% 0.20/0.47    inference(resolution,[],[f177,f85])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) ) | ~spl3_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f176])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f12])).
% 0.20/0.47  fof(f12,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).
% 0.20/0.47  fof(f342,plain,(
% 0.20/0.47    spl3_48 | ~spl3_2 | ~spl3_3 | ~spl3_41),
% 0.20/0.47    inference(avatar_split_clause,[],[f338,f298,f78,f73,f340])).
% 0.20/0.47  fof(f298,plain,(
% 0.20/0.47    spl3_41 <=> ! [X1,X0,X2] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.47  fof(f338,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_41)),
% 0.20/0.47    inference(subsumption_resolution,[],[f337,f80])).
% 0.20/0.47  fof(f337,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m2_connsp_2(X1,sK0,X0)) ) | (~spl3_2 | ~spl3_41)),
% 0.20/0.47    inference(resolution,[],[f299,f75])).
% 0.20/0.47  fof(f299,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) ) | ~spl3_41),
% 0.20/0.47    inference(avatar_component_clause,[],[f298])).
% 0.20/0.47  fof(f307,plain,(
% 0.20/0.47    spl3_42 | ~spl3_10 | ~spl3_39),
% 0.20/0.47    inference(avatar_split_clause,[],[f301,f277,f109,f304])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl3_10 <=> ! [X1,X0,X2] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f301,plain,(
% 0.20/0.47    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (~spl3_10 | ~spl3_39)),
% 0.20/0.47    inference(resolution,[],[f279,f110])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) ) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f109])).
% 0.20/0.47  fof(f300,plain,(
% 0.20/0.47    spl3_41),
% 0.20/0.47    inference(avatar_split_clause,[],[f55,f298])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.20/0.47  fof(f296,plain,(
% 0.20/0.47    spl3_39 | ~spl3_18 | ~spl3_34 | ~spl3_36),
% 0.20/0.47    inference(avatar_split_clause,[],[f295,f258,f248,f152,f277])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    spl3_34 <=> ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.47  fof(f258,plain,(
% 0.20/0.47    spl3_36 <=> ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | r1_tarski(k2_tarski(sK1,X0),k1_tops_1(sK0,sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | (~spl3_18 | ~spl3_34 | ~spl3_36)),
% 0.20/0.47    inference(subsumption_resolution,[],[f294,f154])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    m1_connsp_2(sK2,sK0,sK1) | ~spl3_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f152])).
% 0.20/0.47  fof(f294,plain,(
% 0.20/0.47    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,sK1) | (~spl3_34 | ~spl3_36)),
% 0.20/0.47    inference(resolution,[],[f259,f249])).
% 0.20/0.47  fof(f249,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1)) ) | ~spl3_34),
% 0.20/0.47    inference(avatar_component_clause,[],[f248])).
% 0.20/0.47  fof(f259,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | r1_tarski(k2_tarski(sK1,X0),k1_tops_1(sK0,sK2))) ) | ~spl3_36),
% 0.20/0.47    inference(avatar_component_clause,[],[f258])).
% 0.20/0.47  fof(f287,plain,(
% 0.20/0.47    ~spl3_11 | ~spl3_16 | spl3_40),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f286])).
% 0.20/0.47  fof(f286,plain,(
% 0.20/0.47    $false | (~spl3_11 | ~spl3_16 | spl3_40)),
% 0.20/0.47    inference(subsumption_resolution,[],[f285,f117])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f115])).
% 0.20/0.47  % (22935)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl3_11 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f285,plain,(
% 0.20/0.47    ~r2_hidden(sK1,u1_struct_0(sK0)) | (~spl3_16 | spl3_40)),
% 0.20/0.47    inference(resolution,[],[f283,f144])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) ) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f143])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl3_16 <=> ! [X1,X0] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.47  fof(f283,plain,(
% 0.20/0.47    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_40),
% 0.20/0.47    inference(avatar_component_clause,[],[f281])).
% 0.20/0.47  fof(f284,plain,(
% 0.20/0.47    spl3_39 | ~spl3_40 | ~spl3_23 | ~spl3_38),
% 0.20/0.47    inference(avatar_split_clause,[],[f275,f272,f185,f281,f277])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    spl3_23 <=> m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.47  fof(f272,plain,(
% 0.20/0.47    spl3_38 <=> ! [X1,X0] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k1_tops_1(sK0,X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.47  fof(f275,plain,(
% 0.20/0.47    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | (~spl3_23 | ~spl3_38)),
% 0.20/0.47    inference(resolution,[],[f273,f187])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~spl3_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f185])).
% 0.20/0.47  fof(f273,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k1_tops_1(sK0,X0))) ) | ~spl3_38),
% 0.20/0.47    inference(avatar_component_clause,[],[f272])).
% 0.20/0.47  fof(f274,plain,(
% 0.20/0.47    spl3_38 | ~spl3_2 | ~spl3_3 | ~spl3_37),
% 0.20/0.47    inference(avatar_split_clause,[],[f270,f266,f78,f73,f272])).
% 0.20/0.47  fof(f266,plain,(
% 0.20/0.47    spl3_37 <=> ! [X1,X0,X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.47  fof(f270,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k1_tops_1(sK0,X0))) ) | (~spl3_2 | ~spl3_3 | ~spl3_37)),
% 0.20/0.47    inference(subsumption_resolution,[],[f269,f80])).
% 0.20/0.47  fof(f269,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(X1,k1_tops_1(sK0,X0))) ) | (~spl3_2 | ~spl3_37)),
% 0.20/0.47    inference(resolution,[],[f267,f75])).
% 0.20/0.47  fof(f267,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k1_tops_1(X0,X2))) ) | ~spl3_37),
% 0.20/0.47    inference(avatar_component_clause,[],[f266])).
% 0.20/0.47  fof(f268,plain,(
% 0.20/0.47    spl3_37 | ~spl3_26 | ~spl3_33),
% 0.20/0.47    inference(avatar_split_clause,[],[f245,f242,f204,f266])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    spl3_26 <=> ! [X1,X0,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    spl3_33 <=> ! [X1,X0,X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl3_26 | ~spl3_33)),
% 0.20/0.47    inference(subsumption_resolution,[],[f243,f205])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m2_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f204])).
% 0.20/0.47  fof(f243,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f242])).
% 0.20/0.47  fof(f260,plain,(
% 0.20/0.47    spl3_36 | ~spl3_18 | ~spl3_35),
% 0.20/0.47    inference(avatar_split_clause,[],[f256,f253,f152,f258])).
% 0.20/0.47  fof(f253,plain,(
% 0.20/0.47    spl3_35 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(X1,k1_tops_1(sK0,X0)) | r1_tarski(k2_tarski(sK1,X1),k1_tops_1(sK0,X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.47  fof(f256,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | r1_tarski(k2_tarski(sK1,X0),k1_tops_1(sK0,sK2))) ) | (~spl3_18 | ~spl3_35)),
% 0.20/0.47    inference(resolution,[],[f254,f154])).
% 0.20/0.47  fof(f254,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(X1,k1_tops_1(sK0,X0)) | r1_tarski(k2_tarski(sK1,X1),k1_tops_1(sK0,X0))) ) | ~spl3_35),
% 0.20/0.47    inference(avatar_component_clause,[],[f253])).
% 0.20/0.47  fof(f255,plain,(
% 0.20/0.47    spl3_35 | ~spl3_19 | ~spl3_34),
% 0.20/0.47    inference(avatar_split_clause,[],[f251,f248,f159,f253])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    spl3_19 <=> ! [X1,X0,X2] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(X1,k1_tops_1(sK0,X0)) | r1_tarski(k2_tarski(sK1,X1),k1_tops_1(sK0,X0))) ) | (~spl3_19 | ~spl3_34)),
% 0.20/0.47    inference(resolution,[],[f249,f160])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) ) | ~spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f159])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    spl3_34 | ~spl3_4 | ~spl3_32),
% 0.20/0.47    inference(avatar_split_clause,[],[f246,f238,f83,f248])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    spl3_32 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,X0))) ) | (~spl3_4 | ~spl3_32)),
% 0.20/0.47    inference(resolution,[],[f239,f85])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,k1_tops_1(sK0,X0))) ) | ~spl3_32),
% 0.20/0.47    inference(avatar_component_clause,[],[f238])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    spl3_33),
% 0.20/0.47    inference(avatar_split_clause,[],[f54,f242])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    spl3_32 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_29),
% 0.20/0.47    inference(avatar_split_clause,[],[f236,f218,f78,f73,f68,f238])).
% 0.20/0.47  fof(f218,plain,(
% 0.20/0.47    spl3_29 <=> ! [X1,X0,X2] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.47  fof(f236,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_29)),
% 0.20/0.47    inference(subsumption_resolution,[],[f235,f70])).
% 0.20/0.47  % (22950)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  fof(f235,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_29)),
% 0.20/0.47    inference(subsumption_resolution,[],[f234,f80])).
% 0.20/0.47  fof(f234,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_29)),
% 0.20/0.47    inference(resolution,[],[f219,f75])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | v2_struct_0(X0)) ) | ~spl3_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f218])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    spl3_29),
% 0.20/0.47    inference(avatar_split_clause,[],[f66,f218])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f52,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f206,plain,(
% 0.20/0.48    spl3_26),
% 0.20/0.48    inference(avatar_split_clause,[],[f60,f204])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    spl3_23 | ~spl3_4 | spl3_12 | ~spl3_17 | ~spl3_22),
% 0.20/0.48    inference(avatar_split_clause,[],[f183,f176,f148,f119,f83,f185])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    spl3_17 <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl3_4 | spl3_12 | ~spl3_17 | ~spl3_22)),
% 0.20/0.48    inference(backward_demodulation,[],[f150,f182])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl3_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f148])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    spl3_22),
% 0.20/0.48    inference(avatar_split_clause,[],[f65,f176])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f58,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl3_19),
% 0.20/0.48    inference(avatar_split_clause,[],[f63,f159])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.48    inference(flattening,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.48    inference(nnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    spl3_17 | spl3_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f47,f152,f148])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    spl3_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f64,f143])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f56,f49])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ~spl3_3 | ~spl3_5 | spl3_13),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f131])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    $false | (~spl3_3 | ~spl3_5 | spl3_13)),
% 0.20/0.48    inference(subsumption_resolution,[],[f130,f80])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | (~spl3_5 | spl3_13)),
% 0.20/0.48    inference(resolution,[],[f128,f89])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl3_5 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~l1_struct_0(sK0) | spl3_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f126])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl3_13 <=> l1_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ~spl3_13 | spl3_1 | ~spl3_7 | ~spl3_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f124,f119,f97,f68,f126])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl3_7 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ~l1_struct_0(sK0) | (spl3_1 | ~spl3_7 | ~spl3_12)),
% 0.20/0.48    inference(subsumption_resolution,[],[f123,f70])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_7 | ~spl3_12)),
% 0.20/0.48    inference(resolution,[],[f121,f98])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f119])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    spl3_11 | spl3_12 | ~spl3_4 | ~spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f112,f101,f83,f119,f115])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    spl3_8 <=> ! [X1,X0] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0)) | (~spl3_4 | ~spl3_8)),
% 0.20/0.48    inference(resolution,[],[f102,f85])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) ) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f101])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f62,f109])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f41])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f57,f101])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f51,f97])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f46,f92])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f50,f88])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f45,f83])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f78])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f73])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f68])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (22941)------------------------------
% 0.20/0.48  % (22941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22941)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (22941)Memory used [KB]: 6396
% 0.20/0.48  % (22941)Time elapsed: 0.068 s
% 0.20/0.48  % (22941)------------------------------
% 0.20/0.48  % (22941)------------------------------
% 0.20/0.48  % (22939)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (22942)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (22933)Success in time 0.125 s
%------------------------------------------------------------------------------
