%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1359+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 834 expanded)
%              Number of leaves         :   30 ( 276 expanded)
%              Depth                    :   22
%              Number of atoms          : 1201 (10928 expanded)
%              Number of equality atoms :  259 (3534 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f573,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f84,f89,f93,f97,f101,f105,f158,f166,f174,f182,f190,f196,f207,f229,f335,f572])).

fof(f572,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f85,f570])).

fof(f570,plain,
    ( ~ v1_compts_1(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f569,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ! [X2] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
            | ~ v1_finset_1(X2)
            | ~ r1_tarski(X2,sK1)
            | k1_xboole_0 = X2
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK1)
        & v2_tops_2(sK1,sK0)
        & k1_xboole_0 != sK1
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      | ~ v1_compts_1(sK0) )
    & ( ! [X3] :
          ( ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(X3))
            & v1_finset_1(sK2(X3))
            & r1_tarski(sK2(X3),X3)
            & k1_xboole_0 != sK2(X3)
            & m1_subset_1(sK2(X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
          | ~ v2_tops_2(X3,sK0)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
                  | ~ v1_finset_1(X2)
                  | ~ r1_tarski(X2,X1)
                  | k1_xboole_0 = X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
              & v2_tops_2(X1,X0)
              & k1_xboole_0 != X1
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X4)
                  & v1_finset_1(X4)
                  & r1_tarski(X4,X3)
                  & k1_xboole_0 != X4
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
              | ~ v2_tops_2(X3,X0)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
                | ~ v1_finset_1(X2)
                | ~ r1_tarski(X2,X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
            & k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),X1)
            & v2_tops_2(X1,sK0)
            & k1_xboole_0 != X1
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        | ~ v1_compts_1(sK0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),X4)
                & v1_finset_1(X4)
                & r1_tarski(X4,X3)
                & k1_xboole_0 != X4
                & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
            | ~ v2_tops_2(X3,sK0)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
            | ~ v1_finset_1(X2)
            | ~ r1_tarski(X2,X1)
            | k1_xboole_0 = X2
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),X1)
        & v2_tops_2(X1,sK0)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ! [X2] :
          ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
          | ~ v1_finset_1(X2)
          | ~ r1_tarski(X2,sK1)
          | k1_xboole_0 = X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK1)
      & v2_tops_2(sK1,sK0)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),X4)
          & v1_finset_1(X4)
          & r1_tarski(X4,X3)
          & k1_xboole_0 != X4
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
     => ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(X3))
        & v1_finset_1(sK2(X3))
        & r1_tarski(sK2(X3),X3)
        & k1_xboole_0 != sK2(X3)
        & m1_subset_1(sK2(X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
                | ~ v1_finset_1(X2)
                | ~ r1_tarski(X2,X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
            & v2_tops_2(X1,X0)
            & k1_xboole_0 != X1
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X4)
                & v1_finset_1(X4)
                & r1_tarski(X4,X3)
                & k1_xboole_0 != X4
                & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X3)
            | ~ v2_tops_2(X3,X0)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
                | ~ v1_finset_1(X2)
                | ~ r1_tarski(X2,X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
            & v2_tops_2(X1,X0)
            & k1_xboole_0 != X1
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

% (27999)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f16,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
                | ~ v1_finset_1(X2)
                | ~ r1_tarski(X2,X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
            & v2_tops_2(X1,X0)
            & k1_xboole_0 != X1
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                & v1_finset_1(X2)
                & r1_tarski(X2,X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | k1_xboole_0 = X1
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                     => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                          & v1_finset_1(X2)
                          & r1_tarski(X2,X1)
                          & k1_xboole_0 != X2 ) )
                  & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                  & v2_tops_2(X1,X0)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X2)
                        & v1_finset_1(X2)
                        & r1_tarski(X2,X1)
                        & k1_xboole_0 != X2 ) )
                & k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                & v2_tops_2(X1,X0)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_compts_1)).

fof(f569,plain,
    ( ~ v1_compts_1(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f568,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f568,plain,
    ( ~ v1_compts_1(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f567,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f567,plain,
    ( ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f370,f557])).

fof(f557,plain,
    ( v3_finset_1(sK1)
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f553,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK1
    | spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f553,plain,
    ( v3_finset_1(sK1)
    | k1_xboole_0 = sK1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f552])).

fof(f552,plain,
    ( v3_finset_1(sK1)
    | k1_xboole_0 = sK1
    | v3_finset_1(sK1)
    | k1_xboole_0 = sK1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f510,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),X0)
      | v3_finset_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v3_finset_1(X0)
        | ( k1_xboole_0 = k1_setfam_1(sK4(X0))
          & v1_finset_1(sK4(X0))
          & r1_tarski(sK4(X0),X0)
          & k1_xboole_0 != sK4(X0) )
        | k1_xboole_0 = X0 )
      & ( ( ! [X2] :
              ( k1_xboole_0 != k1_setfam_1(X2)
              | ~ v1_finset_1(X2)
              | ~ r1_tarski(X2,X0)
              | k1_xboole_0 = X2 )
          & k1_xboole_0 != X0 )
        | ~ v3_finset_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k1_setfam_1(X1)
          & v1_finset_1(X1)
          & r1_tarski(X1,X0)
          & k1_xboole_0 != X1 )
     => ( k1_xboole_0 = k1_setfam_1(sK4(X0))
        & v1_finset_1(sK4(X0))
        & r1_tarski(sK4(X0),X0)
        & k1_xboole_0 != sK4(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_finset_1(X0)
        | ? [X1] :
            ( k1_xboole_0 = k1_setfam_1(X1)
            & v1_finset_1(X1)
            & r1_tarski(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = X0 )
      & ( ( ! [X2] :
              ( k1_xboole_0 != k1_setfam_1(X2)
              | ~ v1_finset_1(X2)
              | ~ r1_tarski(X2,X0)
              | k1_xboole_0 = X2 )
          & k1_xboole_0 != X0 )
        | ~ v3_finset_1(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_finset_1(X0)
        | ? [X1] :
            ( k1_xboole_0 = k1_setfam_1(X1)
            & v1_finset_1(X1)
            & r1_tarski(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = X0 )
      & ( ( ! [X1] :
              ( k1_xboole_0 != k1_setfam_1(X1)
              | ~ v1_finset_1(X1)
              | ~ r1_tarski(X1,X0)
              | k1_xboole_0 = X1 )
          & k1_xboole_0 != X0 )
        | ~ v3_finset_1(X0) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_finset_1(X0)
        | ? [X1] :
            ( k1_xboole_0 = k1_setfam_1(X1)
            & v1_finset_1(X1)
            & r1_tarski(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = X0 )
      & ( ( ! [X1] :
              ( k1_xboole_0 != k1_setfam_1(X1)
              | ~ v1_finset_1(X1)
              | ~ r1_tarski(X1,X0)
              | k1_xboole_0 = X1 )
          & k1_xboole_0 != X0 )
        | ~ v3_finset_1(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_finset_1(X0)
    <=> ( ! [X1] :
            ( k1_xboole_0 != k1_setfam_1(X1)
            | ~ v1_finset_1(X1)
            | ~ r1_tarski(X1,X0)
            | k1_xboole_0 = X1 )
        & k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_finset_1(X0)
    <=> ( ! [X1] :
            ~ ( k1_xboole_0 = k1_setfam_1(X1)
              & v1_finset_1(X1)
              & r1_tarski(X1,X0)
              & k1_xboole_0 != X1 )
        & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_finset_1)).

fof(f510,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4(X0),sK1)
        | v3_finset_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f509,f409])).

fof(f409,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f375,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f375,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(resolution,[],[f83,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f509,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4(X0),sK1)
        | v3_finset_1(X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(sK4(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f481,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f481,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(sK4(X1),sK1)
        | v3_finset_1(X1)
        | k1_xboole_0 = X1 )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f480,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_finset_1(sK4(X0))
      | v3_finset_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f480,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(sK4(X1),sK1)
        | ~ v1_finset_1(sK4(X1))
        | v3_finset_1(X1)
        | k1_xboole_0 = X1 )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f476,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK4(X0)
      | v3_finset_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f476,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = sK4(X1)
        | ~ r1_tarski(sK4(X1),sK1)
        | ~ v1_finset_1(sK4(X1))
        | v3_finset_1(X1)
        | k1_xboole_0 = X1 )
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f475])).

fof(f475,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(sK4(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = sK4(X1)
        | ~ r1_tarski(sK4(X1),sK1)
        | ~ v1_finset_1(sK4(X1))
        | v3_finset_1(X1)
        | k1_xboole_0 = X1 )
    | ~ spl5_2 ),
    inference(superposition,[],[f380,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(sK4(X0))
      | v3_finset_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f380,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_setfam_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1)
        | ~ v1_finset_1(X0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_setfam_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1)
        | ~ v1_finset_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f67,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k6_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k6_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k1_setfam_1(X1) = k6_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f67,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X2
        | ~ r1_tarski(X2,sK1)
        | ~ v1_finset_1(X2) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_2
  <=> ! [X2] :
        ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X2
        | ~ r1_tarski(X2,sK1)
        | ~ v1_finset_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f370,plain,
    ( ~ v3_finset_1(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f369,f83])).

fof(f369,plain,
    ( ~ v3_finset_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f347,f75])).

fof(f75,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_4
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f347,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ v3_finset_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(trivial_inequality_removal,[],[f345])).

fof(f345,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_tops_2(sK1,sK0)
    | ~ v3_finset_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(superposition,[],[f46,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_3
  <=> k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f46,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
      | ~ v2_tops_2(X2,X0)
      | ~ v3_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK3(X0))
            & v2_tops_2(sK3(X0),X0)
            & v3_finset_1(sK3(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X2] :
              ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
              | ~ v2_tops_2(X2,X0)
              | ~ v3_finset_1(X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
          & v2_tops_2(X1,X0)
          & v3_finset_1(X1)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK3(X0))
        & v2_tops_2(sK3(X0),X0)
        & v3_finset_1(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
              & v2_tops_2(X1,X0)
              & v3_finset_1(X1)
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X2] :
              ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X2)
              | ~ v2_tops_2(X2,X0)
              | ~ v3_finset_1(X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
              & v2_tops_2(X1,X0)
              & v3_finset_1(X1)
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X1] :
              ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
              | ~ v2_tops_2(X1,X0)
              | ~ v3_finset_1(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | ~ v3_finset_1(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( k1_xboole_0 != k6_setfam_1(u1_struct_0(X0),X1)
            | ~ v2_tops_2(X1,X0)
            | ~ v3_finset_1(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),X1)
                & v2_tops_2(X1,X0)
                & v3_finset_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_compts_1)).

fof(f85,plain,
    ( v1_compts_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f335,plain,
    ( spl5_1
    | ~ spl5_12
    | ~ spl5_16
    | spl5_17
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl5_1
    | ~ spl5_12
    | ~ spl5_16
    | spl5_17
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f333,f33])).

fof(f333,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_12
    | ~ spl5_16
    | spl5_17
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f332,f34])).

fof(f332,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_12
    | ~ spl5_16
    | spl5_17
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f331,f35])).

fof(f331,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_12
    | ~ spl5_16
    | spl5_17
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f330,f64])).

fof(f64,plain,
    ( ~ v1_compts_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f330,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_12
    | ~ spl5_16
    | spl5_17
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(resolution,[],[f313,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v3_finset_1(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f313,plain,
    ( ~ v3_finset_1(sK3(sK0))
    | ~ spl5_12
    | ~ spl5_16
    | spl5_17
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(resolution,[],[f292,f181])).

fof(f181,plain,
    ( r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_18
  <=> r1_tarski(sK2(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK3(sK0)),X0)
        | ~ v3_finset_1(X0) )
    | ~ spl5_12
    | ~ spl5_16
    | spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f291,f173])).

fof(f173,plain,
    ( k1_xboole_0 != sK2(sK3(sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_17
  <=> k1_xboole_0 = sK2(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK3(sK0)),X0)
        | k1_xboole_0 = sK2(sK3(sK0))
        | ~ v3_finset_1(X0) )
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f288,f189])).

fof(f189,plain,
    ( v1_finset_1(sK2(sK3(sK0)))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl5_19
  <=> v1_finset_1(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ v1_finset_1(sK2(sK3(sK0)))
        | ~ r1_tarski(sK2(sK3(sK0)),X0)
        | k1_xboole_0 = sK2(sK3(sK0))
        | ~ v3_finset_1(X0) )
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(trivial_inequality_removal,[],[f285])).

fof(f285,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ v1_finset_1(sK2(sK3(sK0)))
        | ~ r1_tarski(sK2(sK3(sK0)),X0)
        | k1_xboole_0 = sK2(sK3(sK0))
        | ~ v3_finset_1(X0) )
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(superposition,[],[f52,f246])).

fof(f246,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f232,f148])).

fof(f148,plain,
    ( m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_12
  <=> m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f232,plain,
    ( k1_xboole_0 = k1_setfam_1(sK2(sK3(sK0)))
    | ~ m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_16 ),
    inference(superposition,[],[f165,f57])).

fof(f165,plain,
    ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(sK3(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_16
  <=> k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f52,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k1_setfam_1(X2)
      | ~ v1_finset_1(X2)
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X2
      | ~ v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f229,plain,
    ( spl5_1
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl5_1
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f227,f33])).

fof(f227,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f226,f34])).

fof(f226,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f225,f35])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f224,f64])).

fof(f224,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f211,f61])).

fof(f61,plain,(
    ~ v3_finset_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ v3_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f211,plain,
    ( v3_finset_1(k1_xboole_0)
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_14 ),
    inference(superposition,[],[f48,f154])).

fof(f154,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_14
  <=> k1_xboole_0 = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f207,plain,
    ( spl5_1
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl5_1
    | spl5_15 ),
    inference(subsumption_resolution,[],[f205,f33])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | spl5_15 ),
    inference(subsumption_resolution,[],[f204,f34])).

fof(f204,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_15 ),
    inference(subsumption_resolution,[],[f203,f35])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_15 ),
    inference(subsumption_resolution,[],[f201,f64])).

fof(f201,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_15 ),
    inference(resolution,[],[f157,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f157,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl5_15
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f196,plain,
    ( spl5_1
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f194,f33])).

fof(f194,plain,
    ( v2_struct_0(sK0)
    | spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f193,f34])).

fof(f193,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f192,f35])).

fof(f192,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | spl5_13 ),
    inference(subsumption_resolution,[],[f191,f64])).

fof(f191,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(resolution,[],[f151,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v2_tops_2(sK3(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f151,plain,
    ( ~ v2_tops_2(sK3(sK0),sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_13
  <=> v2_tops_2(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f190,plain,
    ( spl5_19
    | ~ spl5_13
    | spl5_14
    | ~ spl5_15
    | spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f186,f91,f63,f156,f153,f150,f188])).

fof(f91,plain,
    ( spl5_8
  <=> ! [X3] :
        ( v1_finset_1(sK2(X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f186,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | v1_finset_1(sK2(sK3(sK0)))
    | spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f185,f33])).

fof(f185,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | v1_finset_1(sK2(sK3(sK0)))
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f184,f34])).

fof(f184,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | v1_finset_1(sK2(sK3(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f183,f35])).

fof(f183,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | v1_finset_1(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f136,f64])).

fof(f136,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | v1_finset_1(sK2(sK3(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(trivial_inequality_removal,[],[f134])).

fof(f134,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | v1_finset_1(sK2(sK3(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(superposition,[],[f92,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_setfam_1(u1_struct_0(X0),sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | v1_finset_1(sK2(X3)) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f182,plain,
    ( spl5_18
    | ~ spl5_13
    | spl5_14
    | ~ spl5_15
    | spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f178,f95,f63,f156,f153,f150,f180])).

fof(f95,plain,
    ( spl5_9
  <=> ! [X3] :
        ( r1_tarski(sK2(X3),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f178,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f177,f33])).

fof(f177,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f176,f34])).

fof(f176,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f175,f35])).

fof(f175,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f137,f64])).

fof(f137,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | r1_tarski(sK2(sK3(sK0)),sK3(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(superposition,[],[f96,f50])).

fof(f96,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | r1_tarski(sK2(X3),X3) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f174,plain,
    ( ~ spl5_17
    | ~ spl5_13
    | spl5_14
    | ~ spl5_15
    | spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f170,f99,f63,f156,f153,f150,f172])).

fof(f99,plain,
    ( spl5_10
  <=> ! [X3] :
        ( k1_xboole_0 != sK2(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f170,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 != sK2(sK3(sK0))
    | spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f169,f33])).

fof(f169,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 != sK2(sK3(sK0))
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f168,f34])).

fof(f168,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 != sK2(sK3(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f167,f35])).

fof(f167,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 != sK2(sK3(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f138,f64])).

% (27991)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f138,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 != sK2(sK3(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 != sK2(sK3(sK0))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(superposition,[],[f100,f50])).

fof(f100,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | k1_xboole_0 != sK2(X3) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f166,plain,
    ( spl5_16
    | ~ spl5_13
    | spl5_14
    | ~ spl5_15
    | spl5_1
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f162,f87,f63,f156,f153,f150,f164])).

fof(f87,plain,
    ( spl5_7
  <=> ! [X3] :
        ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f162,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(sK3(sK0)))
    | spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f161,f33])).

fof(f161,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(sK3(sK0)))
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f160,f34])).

fof(f160,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(sK3(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f159,f35])).

fof(f159,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f139,f64])).

fof(f139,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(sK3(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(sK3(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(superposition,[],[f88,f50])).

fof(f88,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(X3)) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f158,plain,
    ( spl5_12
    | ~ spl5_13
    | spl5_14
    | ~ spl5_15
    | spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f145,f103,f63,f156,f153,f150,f147])).

fof(f103,plain,
    ( spl5_11
  <=> ! [X3] :
        ( m1_subset_1(sK2(X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f145,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_1
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f144,f33])).

fof(f144,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f143,f34])).

fof(f143,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f142,f35])).

fof(f142,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_1
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f140,f64])).

fof(f140,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_11 ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK3(sK0)
    | ~ v2_tops_2(sK3(sK0),sK0)
    | m1_subset_1(sK2(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_11 ),
    inference(superposition,[],[f104,f50])).

fof(f104,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X3
        | ~ v2_tops_2(X3,sK0)
        | m1_subset_1(sK2(X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl5_1
    | spl5_11 ),
    inference(avatar_split_clause,[],[f36,f103,f63])).

fof(f36,plain,(
    ! [X3] :
      ( m1_subset_1(sK2(X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
      | ~ v2_tops_2(X3,sK0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,
    ( spl5_1
    | spl5_10 ),
    inference(avatar_split_clause,[],[f37,f99,f63])).

fof(f37,plain,(
    ! [X3] :
      ( k1_xboole_0 != sK2(X3)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
      | ~ v2_tops_2(X3,sK0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,
    ( spl5_1
    | spl5_9 ),
    inference(avatar_split_clause,[],[f38,f95,f63])).

fof(f38,plain,(
    ! [X3] :
      ( r1_tarski(sK2(X3),X3)
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
      | ~ v2_tops_2(X3,sK0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,
    ( spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f39,f91,f63])).

fof(f39,plain,(
    ! [X3] :
      ( v1_finset_1(sK2(X3))
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
      | ~ v2_tops_2(X3,sK0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,
    ( spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f40,f87,f63])).

fof(f40,plain,(
    ! [X3] :
      ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK2(X3))
      | k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X3)
      | ~ v2_tops_2(X3,sK0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,
    ( ~ spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f41,f82,f63])).

fof(f41,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,
    ( ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f42,f78,f63])).

fof(f42,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f43,f74,f63])).

fof(f43,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f44,f70,f63])).

fof(f44,plain,
    ( k1_xboole_0 = k6_setfam_1(u1_struct_0(sK0),sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f45,f66,f63])).

fof(f45,plain,(
    ! [X2] :
      ( k1_xboole_0 != k6_setfam_1(u1_struct_0(sK0),X2)
      | ~ v1_finset_1(X2)
      | ~ r1_tarski(X2,sK1)
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
