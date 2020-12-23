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
% DateTime   : Thu Dec  3 13:11:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 760 expanded)
%              Number of leaves         :   32 ( 299 expanded)
%              Depth                    :   21
%              Number of atoms          :  778 (10149 expanded)
%              Number of equality atoms :   34 (  89 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f85,f90,f95,f100,f104,f108,f112,f116,f135,f224,f237,f259,f264,f295,f326,f343,f371])).

fof(f371,plain,
    ( ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f369,f89])).

fof(f89,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_5
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f369,plain,
    ( ~ r1_tarski(sK3,sK1)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f368,f94])).

fof(f94,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl10_6
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f368,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | ~ r1_tarski(sK3,sK1)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f359,f84])).

fof(f84,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_4
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f359,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ v3_pre_topc(sK3,sK0)
    | ~ r1_tarski(sK3,sK1)
    | ~ spl10_2
    | ~ spl10_7 ),
    inference(resolution,[],[f99,f75])).

fof(f75,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X3)
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK1) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl10_2
  <=> ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f99,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl10_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f343,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f341,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f341,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f340,f71])).

fof(f71,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl10_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f340,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f338,f80])).

fof(f80,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl10_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f338,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl10_2 ),
    inference(resolution,[],[f75,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( ( ! [X3] :
              ( ~ r2_hidden(sK2,X3)
              | ~ r1_tarski(X3,sK1)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(sK2,sK1) )
        & ( ( r2_hidden(sK2,sK3)
            & r1_tarski(sK3,sK1)
            & v3_pre_topc(sK3,sK0)
            & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(sK2,sK1) ) )
      | ~ v3_pre_topc(sK1,sK0) )
    & ( ! [X5] :
          ( ( r2_hidden(X5,sK1)
            | ! [X6] :
                ( ~ r2_hidden(X5,X6)
                | ~ r1_tarski(X6,sK1)
                | ~ v3_pre_topc(X6,sK0)
                | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) )
          & ( ( r2_hidden(X5,sK4(X5))
              & r1_tarski(sK4(X5),sK1)
              & v3_pre_topc(sK4(X5),sK0)
              & m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X5,sK1) ) )
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f24,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ( ! [X3] :
                        ( ~ r2_hidden(X2,X3)
                        | ~ r1_tarski(X3,X1)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,X1) )
                  & ( ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r1_tarski(X4,X1)
                        & v3_pre_topc(X4,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,X1) ) )
              | ~ v3_pre_topc(X1,X0) )
            & ( ! [X5] :
                  ( ( r2_hidden(X5,X1)
                    | ! [X6] :
                        ( ~ r2_hidden(X5,X6)
                        | ~ r1_tarski(X6,X1)
                        | ~ v3_pre_topc(X6,X0)
                        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  & ( ? [X7] :
                        ( r2_hidden(X5,X7)
                        & r1_tarski(X7,X1)
                        & v3_pre_topc(X7,X0)
                        & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X5,X1) ) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r1_tarski(X3,X1)
                      | ~ v3_pre_topc(X3,sK0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r1_tarski(X4,X1)
                      & v3_pre_topc(X4,sK0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                  | r2_hidden(X2,X1) ) )
            | ~ v3_pre_topc(X1,sK0) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( ~ r2_hidden(X5,X6)
                      | ~ r1_tarski(X6,X1)
                      | ~ v3_pre_topc(X6,sK0)
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) )
                & ( ? [X7] :
                      ( r2_hidden(X5,X7)
                      & r1_tarski(X7,X1)
                      & v3_pre_topc(X7,sK0)
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
                  | ~ r2_hidden(X5,X1) ) )
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r1_tarski(X3,X1)
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ r2_hidden(X2,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X2,X4)
                    & r1_tarski(X4,X1)
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | r2_hidden(X2,X1) ) )
          | ~ v3_pre_topc(X1,sK0) )
        & ( ! [X5] :
              ( ( r2_hidden(X5,X1)
                | ! [X6] :
                    ( ~ r2_hidden(X5,X6)
                    | ~ r1_tarski(X6,X1)
                    | ~ v3_pre_topc(X6,sK0)
                    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) )
              & ( ? [X7] :
                    ( r2_hidden(X5,X7)
                    & r1_tarski(X7,X1)
                    & v3_pre_topc(X7,sK0)
                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ r2_hidden(X5,X1) ) )
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r1_tarski(X3,sK1)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ r2_hidden(X2,sK1) )
            & ( ? [X4] :
                  ( r2_hidden(X2,X4)
                  & r1_tarski(X4,sK1)
                  & v3_pre_topc(X4,sK0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | r2_hidden(X2,sK1) ) )
        | ~ v3_pre_topc(sK1,sK0) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,sK1)
              | ! [X6] :
                  ( ~ r2_hidden(X5,X6)
                  | ~ r1_tarski(X6,sK1)
                  | ~ v3_pre_topc(X6,sK0)
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) )
            & ( ? [X7] :
                  ( r2_hidden(X5,X7)
                  & r1_tarski(X7,sK1)
                  & v3_pre_topc(X7,sK0)
                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ r2_hidden(X5,sK1) ) )
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X2,X3)
              | ~ r1_tarski(X3,sK1)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X2,sK1) )
        & ( ? [X4] :
              ( r2_hidden(X2,X4)
              & r1_tarski(X4,sK1)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X2,sK1) ) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK2,X3)
            | ~ r1_tarski(X3,sK1)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK2,sK1) )
      & ( ? [X4] :
            ( r2_hidden(sK2,X4)
            & r1_tarski(X4,sK1)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK2,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X4] :
        ( r2_hidden(sK2,X4)
        & r1_tarski(X4,sK1)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK2,sK3)
      & r1_tarski(sK3,sK1)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5] :
      ( ? [X7] :
          ( r2_hidden(X5,X7)
          & r1_tarski(X7,sK1)
          & v3_pre_topc(X7,sK0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
     => ( r2_hidden(X5,sK4(X5))
        & r1_tarski(sK4(X5),sK1)
        & v3_pre_topc(sK4(X5),sK0)
        & m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r1_tarski(X3,X1)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r1_tarski(X4,X1)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,X1) ) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( ~ r2_hidden(X5,X6)
                      | ~ r1_tarski(X6,X1)
                      | ~ v3_pre_topc(X6,X0)
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X7] :
                      ( r2_hidden(X5,X7)
                      & r1_tarski(X7,X1)
                      & v3_pre_topc(X7,X0)
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X5,X1) ) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r1_tarski(X3,X1)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r1_tarski(X3,X1)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,X1) ) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r1_tarski(X3,X1)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r1_tarski(X3,X1)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1) ) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r1_tarski(X3,X1)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r1_tarski(X3,X1)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,X1) ) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r1_tarski(X3,X1)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r1_tarski(X3,X1)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1) ) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( r2_hidden(X2,X1)
                <=> ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r1_tarski(X3,X1)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).

fof(f326,plain,
    ( ~ spl10_1
    | spl10_20 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl10_1
    | spl10_20 ),
    inference(subsumption_resolution,[],[f314,f59])).

fof(f314,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl10_1
    | spl10_20 ),
    inference(backward_demodulation,[],[f263,f303])).

fof(f303,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f302,f139])).

fof(f139,plain,(
    sP9 ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | sP9 ),
    inference(subsumption_resolution,[],[f137,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | sP9 ),
    inference(resolution,[],[f121,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ sP8(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP9 ) ),
    inference(cnf_transformation,[],[f66_D])).

fof(f66_D,plain,
    ( ! [X0] :
        ( ~ sP8(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
  <=> ~ sP9 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f121,plain,(
    sP8(sK0) ),
    inference(resolution,[],[f35,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP8(X0) ) ),
    inference(cnf_transformation,[],[f64_D])).

fof(f64_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP8(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f302,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ sP9
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f301,f34])).

fof(f301,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ sP9
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f122,f71])).

fof(f122,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ sP9 ),
    inference(resolution,[],[f35,f67])).

fof(f67,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ l1_pre_topc(X1)
      | ~ sP9 ) ),
    inference(general_splitting,[],[f65,f66_D])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP8(X0) ) ),
    inference(general_splitting,[],[f48,f64_D])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f263,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl10_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl10_20
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f295,plain,
    ( ~ spl10_17
    | spl10_20 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl10_17
    | spl10_20 ),
    inference(subsumption_resolution,[],[f292,f263])).

fof(f292,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl10_17 ),
    inference(resolution,[],[f223,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f223,plain,
    ( r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl10_17
  <=> r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f264,plain,
    ( ~ spl10_20
    | spl10_13 ),
    inference(avatar_split_clause,[],[f153,f132,f261])).

fof(f132,plain,
    ( spl10_13
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f153,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f125,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f125,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f118,f34])).

fof(f118,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f259,plain,(
    ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f257,f136])).

fof(f136,plain,(
    ~ sP7 ),
    inference(subsumption_resolution,[],[f120,f34])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ sP7 ),
    inference(resolution,[],[f35,f63])).

fof(f63,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP7 ) ),
    inference(general_splitting,[],[f61,f62_D])).

fof(f62,plain,(
    ! [X0] :
      ( ~ sP6(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP7 ) ),
    inference(cnf_transformation,[],[f62_D])).

fof(f62_D,plain,
    ( ! [X0] :
        ( ~ sP6(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
  <=> ~ sP7 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f49,f60_D])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0)
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f60_D])).

fof(f60_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | k1_tops_1(X0,X2) != X2
          | v3_pre_topc(X2,X0) )
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f257,plain,
    ( sP7
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f256,f34])).

fof(f256,plain,
    ( ~ l1_pre_topc(sK0)
    | sP7
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f255,f33])).

fof(f255,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | sP7
    | ~ spl10_12 ),
    inference(resolution,[],[f130,f62])).

fof(f130,plain,
    ( sP6(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl10_12
  <=> sP6(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f237,plain,
    ( spl10_13
    | spl10_16 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl10_13
    | spl10_16 ),
    inference(subsumption_resolution,[],[f234,f154])).

fof(f154,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl10_13 ),
    inference(subsumption_resolution,[],[f153,f134])).

fof(f134,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f132])).

fof(f234,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl10_16 ),
    inference(resolution,[],[f219,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f219,plain,
    ( ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl10_16
  <=> r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f224,plain,
    ( ~ spl10_16
    | spl10_17
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_13 ),
    inference(avatar_split_clause,[],[f214,f132,f114,f110,f106,f102,f221,f217])).

fof(f102,plain,
    ( spl10_8
  <=> ! [X5] :
        ( r2_hidden(X5,sK4(X5))
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f106,plain,
    ( spl10_9
  <=> ! [X5] :
        ( r1_tarski(sK4(X5),sK1)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f110,plain,
    ( spl10_10
  <=> ! [X5] :
        ( v3_pre_topc(sK4(X5),sK0)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f114,plain,
    ( spl10_11
  <=> ! [X5] :
        ( m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f214,plain,
    ( r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_13 ),
    inference(resolution,[],[f208,f141])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK4(X0),X1)
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_8 ),
    inference(resolution,[],[f103,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK4(X5))
        | ~ r2_hidden(X5,sK1) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f208,plain,
    ( r1_tarski(sK4(sK5(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_13 ),
    inference(subsumption_resolution,[],[f206,f154])).

fof(f206,plain,
    ( r1_tarski(sK4(sK5(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_11
    | spl10_13 ),
    inference(superposition,[],[f184,f200])).

fof(f200,plain,
    ( sK4(sK5(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK4(sK5(sK1,k1_tops_1(sK0,sK1))))
    | ~ spl10_10
    | ~ spl10_11
    | spl10_13 ),
    inference(resolution,[],[f173,f154])).

fof(f173,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | sK4(sK5(sK1,X0)) = k1_tops_1(sK0,sK4(sK5(sK1,X0))) )
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(resolution,[],[f166,f54])).

fof(f166,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK1)
        | sK4(X6) = k1_tops_1(sK0,sK4(X6)) )
    | ~ spl10_10
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f165,f111])).

fof(f111,plain,
    ( ! [X5] :
        ( v3_pre_topc(sK4(X5),sK0)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f165,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK1)
        | ~ v3_pre_topc(sK4(X6),sK0)
        | sK4(X6) = k1_tops_1(sK0,sK4(X6)) )
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f164,f139])).

fof(f164,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK1)
        | ~ v3_pre_topc(sK4(X6),sK0)
        | sK4(X6) = k1_tops_1(sK0,sK4(X6))
        | ~ sP9 )
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f160,f34])).

fof(f160,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK1)
        | ~ v3_pre_topc(sK4(X6),sK0)
        | sK4(X6) = k1_tops_1(sK0,sK4(X6))
        | ~ l1_pre_topc(sK0)
        | ~ sP9 )
    | ~ spl10_11 ),
    inference(resolution,[],[f115,f67])).

fof(f115,plain,
    ( ! [X5] :
        ( m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,sK1) )
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f184,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK4(sK5(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(resolution,[],[f183,f54])).

fof(f183,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r1_tarski(k1_tops_1(sK0,sK4(X1)),k1_tops_1(sK0,sK1)) )
    | ~ spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f182,f107])).

fof(f107,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r1_tarski(sK4(X5),sK1) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f182,plain,
    ( ! [X1] :
        ( r1_tarski(k1_tops_1(sK0,sK4(X1)),k1_tops_1(sK0,sK1))
        | ~ r1_tarski(sK4(X1),sK1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl10_11 ),
    inference(resolution,[],[f124,f115])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f117,f34])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f135,plain,
    ( spl10_12
    | ~ spl10_13
    | spl10_1 ),
    inference(avatar_split_clause,[],[f126,f70,f132,f128])).

fof(f126,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | sP6(sK0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f119,f72])).

fof(f72,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f119,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | sP6(sK0) ),
    inference(resolution,[],[f35,f60])).

fof(f116,plain,
    ( spl10_1
    | spl10_11 ),
    inference(avatar_split_clause,[],[f36,f114,f70])).

fof(f36,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X5,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,
    ( spl10_1
    | spl10_10 ),
    inference(avatar_split_clause,[],[f37,f110,f70])).

fof(f37,plain,(
    ! [X5] :
      ( v3_pre_topc(sK4(X5),sK0)
      | ~ r2_hidden(X5,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f108,plain,
    ( spl10_1
    | spl10_9 ),
    inference(avatar_split_clause,[],[f38,f106,f70])).

fof(f38,plain,(
    ! [X5] :
      ( r1_tarski(sK4(X5),sK1)
      | ~ r2_hidden(X5,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,
    ( spl10_1
    | spl10_8 ),
    inference(avatar_split_clause,[],[f39,f102,f70])).

fof(f39,plain,(
    ! [X5] :
      ( r2_hidden(X5,sK4(X5))
      | ~ r2_hidden(X5,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,
    ( ~ spl10_1
    | spl10_3
    | spl10_7 ),
    inference(avatar_split_clause,[],[f41,f97,f78,f70])).

fof(f41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,
    ( ~ spl10_1
    | spl10_3
    | spl10_6 ),
    inference(avatar_split_clause,[],[f42,f92,f78,f70])).

fof(f42,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,
    ( ~ spl10_1
    | spl10_3
    | spl10_5 ),
    inference(avatar_split_clause,[],[f43,f87,f78,f70])).

fof(f43,plain,
    ( r1_tarski(sK3,sK1)
    | r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,
    ( ~ spl10_1
    | spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f44,f82,f78,f70])).

fof(f44,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f68,f74,f70])).

fof(f68,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f45,f53])).

fof(f45,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,X3)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (19876)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.46  % (19892)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (19873)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19870)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19891)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (19878)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (19886)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (19877)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (19881)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (19874)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (19872)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (19879)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (19869)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (19877)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f76,f85,f90,f95,f100,f104,f108,f112,f116,f135,f224,f237,f259,f264,f295,f326,f343,f371])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    ~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f370])).
% 0.21/0.53  fof(f370,plain,(
% 0.21/0.53    $false | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f369,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    r1_tarski(sK3,sK1) | ~spl10_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl10_5 <=> r1_tarski(sK3,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    ~r1_tarski(sK3,sK1) | (~spl10_2 | ~spl10_4 | ~spl10_6 | ~spl10_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f368,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    v3_pre_topc(sK3,sK0) | ~spl10_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl10_6 <=> v3_pre_topc(sK3,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    ~v3_pre_topc(sK3,sK0) | ~r1_tarski(sK3,sK1) | (~spl10_2 | ~spl10_4 | ~spl10_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f359,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    r2_hidden(sK2,sK3) | ~spl10_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl10_4 <=> r2_hidden(sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    ~r2_hidden(sK2,sK3) | ~v3_pre_topc(sK3,sK0) | ~r1_tarski(sK3,sK1) | (~spl10_2 | ~spl10_7)),
% 0.21/0.53    inference(resolution,[],[f99,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,X3) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1)) ) | ~spl10_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl10_2 <=> ! [X3] : (~r2_hidden(sK2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl10_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl10_7 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.53  fof(f343,plain,(
% 0.21/0.53    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f342])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    $false | (~spl10_1 | ~spl10_2 | ~spl10_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f341,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK1) | (~spl10_1 | ~spl10_2 | ~spl10_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f340,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    v3_pre_topc(sK1,sK0) | ~spl10_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl10_1 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | (~spl10_2 | ~spl10_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f338,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    r2_hidden(sK2,sK1) | ~spl10_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl10_3 <=> r2_hidden(sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | ~spl10_2),
% 0.21/0.53    inference(resolution,[],[f75,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ((((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2,sK1)) & ((r2_hidden(sK2,sK3) & r1_tarski(sK3,sK1) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK2,sK1))) | ~v3_pre_topc(sK1,sK0)) & (! [X5] : ((r2_hidden(X5,sK1) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,sK1) | ~v3_pre_topc(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))))) & ((r2_hidden(X5,sK4(X5)) & r1_tarski(sK4(X5),sK1) & v3_pre_topc(sK4(X5),sK0) & m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X5,sK1))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f24,f23,f22,f21,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1))) | ~v3_pre_topc(X1,X0)) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X1) | ~v3_pre_topc(X6,X0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X1) & v3_pre_topc(X7,X0) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X2,X1))) | ~v3_pre_topc(X1,sK0)) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X1) | ~v3_pre_topc(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X1) & v3_pre_topc(X7,sK0) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X5,X1))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X1] : ((? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X2,X1))) | ~v3_pre_topc(X1,sK0)) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X1) | ~v3_pre_topc(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X1) & v3_pre_topc(X7,sK0) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X5,X1))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X2,sK1)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,sK1) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X2,sK1))) | ~v3_pre_topc(sK1,sK0)) & (! [X5] : ((r2_hidden(X5,sK1) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,sK1) | ~v3_pre_topc(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,sK1) & v3_pre_topc(X7,sK0) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X5,sK1))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X2,sK1)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,sK1) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X2,sK1))) => ((! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2,sK1)) & (? [X4] : (r2_hidden(sK2,X4) & r1_tarski(X4,sK1) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK2,sK1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X4] : (r2_hidden(sK2,X4) & r1_tarski(X4,sK1) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK2,sK3) & r1_tarski(sK3,sK1) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X5] : (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,sK1) & v3_pre_topc(X7,sK0) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(X5,sK4(X5)) & r1_tarski(sK4(X5),sK1) & v3_pre_topc(sK4(X5),sK0) & m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1))) | ~v3_pre_topc(X1,X0)) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X1) | ~v3_pre_topc(X6,X0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X1) & v3_pre_topc(X7,X0) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(rectify,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1))) | ~v3_pre_topc(X1,X0)) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1))) | ~v3_pre_topc(X1,X0)) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    ~spl10_1 | spl10_20),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f325])).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    $false | (~spl10_1 | spl10_20)),
% 0.21/0.53    inference(subsumption_resolution,[],[f314,f59])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK1) | (~spl10_1 | spl10_20)),
% 0.21/0.53    inference(backward_demodulation,[],[f263,f303])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    sK1 = k1_tops_1(sK0,sK1) | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f302,f139])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    sP9),
% 0.21/0.53    inference(subsumption_resolution,[],[f138,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | sP9),
% 0.21/0.53    inference(subsumption_resolution,[],[f137,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | sP9),
% 0.21/0.53    inference(resolution,[],[f121,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0] : (~sP8(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP9) )),
% 0.21/0.53    inference(cnf_transformation,[],[f66_D])).
% 0.21/0.53  fof(f66_D,plain,(
% 0.21/0.53    ( ! [X0] : (~sP8(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) <=> ~sP9),
% 0.21/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    sP8(sK0)),
% 0.21/0.53    inference(resolution,[],[f35,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP8(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f64_D])).
% 0.21/0.53  fof(f64_D,plain,(
% 0.21/0.53    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP8(X0)) )),
% 0.21/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    sK1 = k1_tops_1(sK0,sK1) | ~sP9 | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f301,f34])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~sP9 | ~spl10_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f71])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~sP9),
% 0.21/0.53    inference(resolution,[],[f35,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~sP9) )),
% 0.21/0.53    inference(general_splitting,[],[f65,f66_D])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP8(X0)) )),
% 0.21/0.53    inference(general_splitting,[],[f48,f64_D])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl10_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f261])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    spl10_20 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    ~spl10_17 | spl10_20),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f294])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    $false | (~spl10_17 | spl10_20)),
% 0.21/0.53    inference(subsumption_resolution,[],[f292,f263])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl10_17),
% 0.21/0.53    inference(resolution,[],[f223,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl10_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f221])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    spl10_17 <=> r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ~spl10_20 | spl10_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f153,f132,f261])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl10_13 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f125,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f118,f34])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f35,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ~spl10_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f258])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    $false | ~spl10_12),
% 0.21/0.53    inference(subsumption_resolution,[],[f257,f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ~sP7),
% 0.21/0.53    inference(subsumption_resolution,[],[f120,f34])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~sP7),
% 0.21/0.53    inference(resolution,[],[f35,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP7) )),
% 0.21/0.53    inference(general_splitting,[],[f61,f62_D])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (~sP6(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP7) )),
% 0.21/0.53    inference(cnf_transformation,[],[f62_D])).
% 0.21/0.53  fof(f62_D,plain,(
% 0.21/0.53    ( ! [X0] : (~sP6(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) <=> ~sP7),
% 0.21/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) )),
% 0.21/0.53    inference(general_splitting,[],[f49,f60_D])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0) | sP6(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f60_D])).
% 0.21/0.54  fof(f60_D,plain,(
% 0.21/0.54    ( ! [X0] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0)) ) <=> ~sP6(X0)) )),
% 0.21/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    sP7 | ~spl10_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f256,f34])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | sP7 | ~spl10_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f255,f33])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | sP7 | ~spl10_12),
% 0.21/0.54    inference(resolution,[],[f130,f62])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    sP6(sK0) | ~spl10_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl10_12 <=> sP6(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    spl10_13 | spl10_16),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    $false | (spl10_13 | spl10_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f234,f154])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl10_13),
% 0.21/0.54    inference(subsumption_resolution,[],[f153,f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    sK1 != k1_tops_1(sK0,sK1) | spl10_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f132])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl10_16),
% 0.21/0.54    inference(resolution,[],[f219,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ~r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1) | spl10_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f217])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    spl10_16 <=> r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    ~spl10_16 | spl10_17 | ~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | spl10_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f214,f132,f114,f110,f106,f102,f221,f217])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl10_8 <=> ! [X5] : (r2_hidden(X5,sK4(X5)) | ~r2_hidden(X5,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    spl10_9 <=> ! [X5] : (r1_tarski(sK4(X5),sK1) | ~r2_hidden(X5,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    spl10_10 <=> ! [X5] : (v3_pre_topc(sK4(X5),sK0) | ~r2_hidden(X5,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl10_11 <=> ! [X5] : (m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X5,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1) | (~spl10_8 | ~spl10_9 | ~spl10_10 | ~spl10_11 | spl10_13)),
% 0.21/0.54    inference(resolution,[],[f208,f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(sK4(X0),X1) | r2_hidden(X0,X1) | ~r2_hidden(X0,sK1)) ) | ~spl10_8),
% 0.21/0.54    inference(resolution,[],[f103,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(X5,sK4(X5)) | ~r2_hidden(X5,sK1)) ) | ~spl10_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    r1_tarski(sK4(sK5(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | (~spl10_9 | ~spl10_10 | ~spl10_11 | spl10_13)),
% 0.21/0.54    inference(subsumption_resolution,[],[f206,f154])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    r1_tarski(sK4(sK5(sK1,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl10_9 | ~spl10_10 | ~spl10_11 | spl10_13)),
% 0.21/0.54    inference(superposition,[],[f184,f200])).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    sK4(sK5(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK4(sK5(sK1,k1_tops_1(sK0,sK1)))) | (~spl10_10 | ~spl10_11 | spl10_13)),
% 0.21/0.54    inference(resolution,[],[f173,f154])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK1,X0) | sK4(sK5(sK1,X0)) = k1_tops_1(sK0,sK4(sK5(sK1,X0)))) ) | (~spl10_10 | ~spl10_11)),
% 0.21/0.54    inference(resolution,[],[f166,f54])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,sK1) | sK4(X6) = k1_tops_1(sK0,sK4(X6))) ) | (~spl10_10 | ~spl10_11)),
% 0.21/0.54    inference(subsumption_resolution,[],[f165,f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X5] : (v3_pre_topc(sK4(X5),sK0) | ~r2_hidden(X5,sK1)) ) | ~spl10_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f110])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,sK1) | ~v3_pre_topc(sK4(X6),sK0) | sK4(X6) = k1_tops_1(sK0,sK4(X6))) ) | ~spl10_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f164,f139])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,sK1) | ~v3_pre_topc(sK4(X6),sK0) | sK4(X6) = k1_tops_1(sK0,sK4(X6)) | ~sP9) ) | ~spl10_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f160,f34])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,sK1) | ~v3_pre_topc(sK4(X6),sK0) | sK4(X6) = k1_tops_1(sK0,sK4(X6)) | ~l1_pre_topc(sK0) | ~sP9) ) | ~spl10_11),
% 0.21/0.54    inference(resolution,[],[f115,f67])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X5] : (m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X5,sK1)) ) | ~spl10_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f114])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK4(sK5(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl10_9 | ~spl10_11)),
% 0.21/0.54    inference(resolution,[],[f183,f54])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(k1_tops_1(sK0,sK4(X1)),k1_tops_1(sK0,sK1))) ) | (~spl10_9 | ~spl10_11)),
% 0.21/0.54    inference(subsumption_resolution,[],[f182,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X5] : (~r2_hidden(X5,sK1) | r1_tarski(sK4(X5),sK1)) ) | ~spl10_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f106])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k1_tops_1(sK0,sK4(X1)),k1_tops_1(sK0,sK1)) | ~r1_tarski(sK4(X1),sK1) | ~r2_hidden(X1,sK1)) ) | ~spl10_11),
% 0.21/0.54    inference(resolution,[],[f124,f115])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f117,f34])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f35,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    spl10_12 | ~spl10_13 | spl10_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f126,f70,f132,f128])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    sK1 != k1_tops_1(sK0,sK1) | sP6(sK0) | spl10_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f119,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ~v3_pre_topc(sK1,sK0) | spl10_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f70])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | sP6(sK0)),
% 0.21/0.54    inference(resolution,[],[f35,f60])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl10_1 | spl10_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f114,f70])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X5] : (m1_subset_1(sK4(X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X5,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    spl10_1 | spl10_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f110,f70])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X5] : (v3_pre_topc(sK4(X5),sK0) | ~r2_hidden(X5,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl10_1 | spl10_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f106,f70])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X5] : (r1_tarski(sK4(X5),sK1) | ~r2_hidden(X5,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    spl10_1 | spl10_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f102,f70])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X5] : (r2_hidden(X5,sK4(X5)) | ~r2_hidden(X5,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ~spl10_1 | spl10_3 | spl10_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f97,f78,f70])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ~spl10_1 | spl10_3 | spl10_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f92,f78,f70])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v3_pre_topc(sK3,sK0) | r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ~spl10_1 | spl10_3 | spl10_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f87,f78,f70])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    r1_tarski(sK3,sK1) | r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ~spl10_1 | spl10_3 | spl10_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f82,f78,f70])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    r2_hidden(sK2,sK3) | r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ~spl10_1 | spl10_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f68,f74,f70])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f45,f53])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (19877)------------------------------
% 0.21/0.54  % (19877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19877)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (19877)Memory used [KB]: 10874
% 0.21/0.54  % (19877)Time elapsed: 0.119 s
% 0.21/0.54  % (19877)------------------------------
% 0.21/0.54  % (19877)------------------------------
% 0.21/0.54  % (19883)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (19868)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (19897)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (19898)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (19888)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (19895)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (19875)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (19887)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (19884)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (19889)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (19896)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (19867)Success in time 0.192 s
%------------------------------------------------------------------------------
