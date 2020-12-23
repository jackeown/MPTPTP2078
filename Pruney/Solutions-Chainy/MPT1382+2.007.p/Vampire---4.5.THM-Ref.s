%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 396 expanded)
%              Number of leaves         :   15 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :  408 (3308 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f244,f256,f283,f285])).

fof(f285,plain,
    ( ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f264,f276])).

fof(f276,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl4_11
  <=> v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f264,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl4_10 ),
    inference(resolution,[],[f242,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f242,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl4_10
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f283,plain,
    ( ~ spl4_9
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl4_9
    | spl4_11 ),
    inference(subsumption_resolution,[],[f272,f277])).

fof(f277,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f275])).

fof(f272,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f268,f80])).

fof(f80,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,u1_struct_0(sK0)),sK2)
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_connsp_2(X3,sK0,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | v1_xboole_0(X3) )
                & m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_connsp_2(X3,sK0,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_connsp_2(X3,sK0,sK1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_connsp_2(X3,sK0,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ! [X3] :
          ( ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_connsp_2(X3,sK0,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
          | v1_xboole_0(X3) )
      & m1_connsp_2(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_tops_1(sK0,sK2),X0),sK2)
      | r1_tarski(k1_tops_1(sK0,sK2),X0) ) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f72,f45])).

fof(f72,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f70,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f268,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f267,f72])).

fof(f267,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f265,f97])).

fof(f97,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f96,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f94,f34])).

fof(f94,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f44,f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f265,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(resolution,[],[f239,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | ~ v3_pre_topc(X0,sK0)
      | ~ r1_tarski(X0,sK2)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ r1_tarski(X3,sK2)
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f239,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl4_9
  <=> m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f256,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f254,f50])).

fof(f254,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl4_10 ),
    inference(subsumption_resolution,[],[f253,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f253,plain,
    ( v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl4_10 ),
    inference(subsumption_resolution,[],[f252,f33])).

fof(f252,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl4_10 ),
    inference(subsumption_resolution,[],[f251,f34])).

fof(f251,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl4_10 ),
    inference(subsumption_resolution,[],[f250,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f250,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl4_10 ),
    inference(subsumption_resolution,[],[f246,f37])).

fof(f37,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f246,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | spl4_10 ),
    inference(resolution,[],[f243,f142])).

% (14635)Refutation not found, incomplete strategy% (14635)------------------------------
% (14635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f142,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,k1_tops_1(X2,X1))
      | ~ m1_connsp_2(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ r1_tarski(X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f40,f49])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f243,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f241])).

fof(f244,plain,
    ( spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f235,f241,f237])).

fof(f235,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f220,f97])).

fof(f220,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f216,f80])).

fof(f216,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X0)
      | m1_connsp_2(X0,sK0,sK1)
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f215,f32])).

fof(f215,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(sK1,X0)
      | m1_connsp_2(X0,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f214,f33])).

fof(f214,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(sK1,X0)
      | m1_connsp_2(X0,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f213,f34])).

fof(f213,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(sK1,X0)
      | m1_connsp_2(X0,sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f212,f35])).

fof(f212,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ v3_pre_topc(X2,X3)
      | ~ r2_hidden(X1,X2)
      | m1_connsp_2(X2,X3,X1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r1_tarski(X2,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f42,f49])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (14620)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % (14627)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.47  % (14627)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (14635)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f286,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f244,f256,f283,f285])).
% 0.20/0.47  fof(f285,plain,(
% 0.20/0.47    ~spl4_10 | ~spl4_11),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.47  fof(f284,plain,(
% 0.20/0.47    $false | (~spl4_10 | ~spl4_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f264,f276])).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~spl4_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f275])).
% 0.20/0.47  fof(f275,plain,(
% 0.20/0.47    spl4_11 <=> v1_xboole_0(k1_tops_1(sK0,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.47  fof(f264,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_tops_1(sK0,sK2)) | ~spl4_10),
% 0.20/0.47    inference(resolution,[],[f242,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f241])).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    spl4_10 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f283,plain,(
% 0.20/0.47    ~spl4_9 | spl4_11),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f282])).
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    $false | (~spl4_9 | spl4_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f272,f277])).
% 0.20/0.47  fof(f277,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_tops_1(sK0,sK2)) | spl4_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f275])).
% 0.20/0.47  fof(f272,plain,(
% 0.20/0.47    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~spl4_9),
% 0.20/0.47    inference(subsumption_resolution,[],[f268,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f76])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f74,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_hidden(sK3(X1,u1_struct_0(sK0)),sK2) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(resolution,[],[f55,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2)) )),
% 0.20/0.47    inference(resolution,[],[f45,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.47    inference(resolution,[],[f48,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK3(k1_tops_1(sK0,sK2),X0),sK2) | r1_tarski(k1_tops_1(sK0,sK2),X0)) )),
% 0.20/0.47    inference(resolution,[],[f73,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | r2_hidden(X0,sK2)) )),
% 0.20/0.47    inference(resolution,[],[f72,f45])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f70,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 0.20/0.47    inference(resolution,[],[f39,f36])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.47  fof(f268,plain,(
% 0.20/0.47    v1_xboole_0(k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~spl4_9),
% 0.20/0.47    inference(subsumption_resolution,[],[f267,f72])).
% 0.20/0.47  fof(f267,plain,(
% 0.20/0.47    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | v1_xboole_0(k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~spl4_9),
% 0.20/0.47    inference(subsumption_resolution,[],[f265,f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f96,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f94,f34])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.47    inference(resolution,[],[f44,f36])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.47  fof(f265,plain,(
% 0.20/0.47    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | v1_xboole_0(k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~spl4_9),
% 0.20/0.47    inference(resolution,[],[f239,f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK2) | v1_xboole_0(X0) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(resolution,[],[f38,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~r1_tarski(X3,sK2) | v1_xboole_0(X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~spl4_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f237])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    spl4_9 <=> m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.47  fof(f256,plain,(
% 0.20/0.47    spl4_10),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f255])).
% 0.20/0.47  fof(f255,plain,(
% 0.20/0.47    $false | spl4_10),
% 0.20/0.47    inference(subsumption_resolution,[],[f254,f50])).
% 0.20/0.47  fof(f254,plain,(
% 0.20/0.47    ~r1_tarski(sK2,u1_struct_0(sK0)) | spl4_10),
% 0.20/0.47    inference(subsumption_resolution,[],[f253,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f253,plain,(
% 0.20/0.47    v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl4_10),
% 0.20/0.47    inference(subsumption_resolution,[],[f252,f33])).
% 0.20/0.47  fof(f252,plain,(
% 0.20/0.47    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl4_10),
% 0.20/0.47    inference(subsumption_resolution,[],[f251,f34])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl4_10),
% 0.20/0.47    inference(subsumption_resolution,[],[f250,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl4_10),
% 0.20/0.47    inference(subsumption_resolution,[],[f246,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    ~m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(sK2,u1_struct_0(sK0)) | spl4_10),
% 0.20/0.47    inference(resolution,[],[f243,f142])).
% 0.20/0.47  % (14635)Refutation not found, incomplete strategy% (14635)------------------------------
% 0.20/0.47  % (14635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ( ! [X2,X3,X1] : (r2_hidden(X3,k1_tops_1(X2,X1)) | ~m1_connsp_2(X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~r1_tarski(X1,u1_struct_0(X2))) )),
% 0.20/0.48    inference(resolution,[],[f40,f49])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.48  fof(f243,plain,(
% 0.20/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f241])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    spl4_9 | ~spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f235,f241,f237])).
% 0.20/0.48  fof(f235,plain,(
% 0.20/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f220,f97])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.48    inference(resolution,[],[f216,f80])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,X0) | m1_connsp_2(X0,sK0,sK1) | ~v3_pre_topc(X0,sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f215,f32])).
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0) | m1_connsp_2(X0,sK0,sK1) | v2_struct_0(sK0) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f214,f33])).
% 0.20/0.48  fof(f214,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0) | m1_connsp_2(X0,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f213,f34])).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0) | m1_connsp_2(X0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.20/0.48    inference(resolution,[],[f212,f35])).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    ( ! [X2,X3,X1] : (~m1_subset_1(X1,u1_struct_0(X3)) | ~v3_pre_topc(X2,X3) | ~r2_hidden(X1,X2) | m1_connsp_2(X2,X3,X1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~r1_tarski(X2,u1_struct_0(X3))) )),
% 0.20/0.48    inference(resolution,[],[f42,f49])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_connsp_2(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (14627)------------------------------
% 0.20/0.48  % (14627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (14627)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (14627)Memory used [KB]: 5500
% 0.20/0.48  % (14627)Time elapsed: 0.051 s
% 0.20/0.48  % (14627)------------------------------
% 0.20/0.48  % (14627)------------------------------
% 0.20/0.48  % (14619)Success in time 0.116 s
%------------------------------------------------------------------------------
