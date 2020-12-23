%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:47 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 317 expanded)
%              Number of leaves         :   30 ( 126 expanded)
%              Depth                    :   15
%              Number of atoms          :  640 (2409 expanded)
%              Number of equality atoms :   63 ( 358 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f104,f106,f115,f133,f136,f138,f154,f168,f170,f172,f176,f178,f183,f186])).

fof(f186,plain,
    ( spl4_1
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl4_1
    | ~ spl4_14 ),
    inference(resolution,[],[f184,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | ! [X5] :
          ( sK3 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
    & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( X3 != X4
                          | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                      | ! [X5] :
                          ( X3 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                    & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2))) )
          & ~ r1_tsep_1(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2))) )
        & ~ r1_tsep_1(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          | ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
        & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
   => ( ( ! [X4] :
            ( sK3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        | ! [X5] :
            ( sK3 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
      & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f184,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | spl4_1
    | ~ spl4_14 ),
    inference(resolution,[],[f175,f71])).

fof(f71,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_1
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f175,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_14
  <=> ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f183,plain,
    ( spl4_2
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f181,f44])).

fof(f181,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f153,f75])).

fof(f75,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f153,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_12
  <=> ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f178,plain,
    ( spl4_9
    | ~ spl4_8
    | spl4_3
    | ~ spl4_7
    | spl4_4
    | ~ spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f177,f144,f165,f98,f122,f94,f126,f130])).

fof(f130,plain,
    ( spl4_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f126,plain,
    ( spl4_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f94,plain,
    ( spl4_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f122,plain,
    ( spl4_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f98,plain,
    ( spl4_4
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f165,plain,
    ( spl4_13
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f144,plain,
    ( spl4_10
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f177,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f146,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f146,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f176,plain,
    ( spl4_10
    | ~ spl4_11
    | spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f161,f118,f174,f148,f144])).

fof(f148,plain,
    ( spl4_11
  <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f118,plain,
    ( spl4_6
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f161,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
        | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f141,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X0),X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(X0,X1)
      | ~ m1_subset_1(X0,X2) ) ),
    inference(resolution,[],[f82,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

% (25016)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f60,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f141,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(superposition,[],[f63,f120])).

fof(f120,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f172,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_9 ),
    inference(resolution,[],[f132,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f132,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f170,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f167,f42])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f167,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f168,plain,
    ( spl4_9
    | spl4_3
    | ~ spl4_7
    | spl4_4
    | ~ spl4_13
    | ~ spl4_8
    | spl4_11 ),
    inference(avatar_split_clause,[],[f163,f148,f126,f165,f98,f122,f94,f130])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | spl4_11 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_11 ),
    inference(resolution,[],[f160,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) )
    | spl4_11 ),
    inference(resolution,[],[f159,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f159,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl4_11 ),
    inference(resolution,[],[f150,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f150,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f154,plain,
    ( spl4_10
    | ~ spl4_11
    | spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f142,f118,f152,f148,f144])).

fof(f142,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
        | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f140,f84])).

fof(f140,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2))
    | ~ spl4_6 ),
    inference(superposition,[],[f78,f120])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f63,f64])).

fof(f64,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f52,f53,f53])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f138,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f124,f40])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f136,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f128,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f128,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f133,plain,
    ( spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f116,f102,f130,f126,f122,f118])).

fof(f102,plain,
    ( spl4_5
  <=> ! [X0] :
        ( u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f116,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl4_5 ),
    inference(resolution,[],[f103,f42])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f115,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f100,plain,
    ( v2_struct_0(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f106,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl4_3 ),
    inference(resolution,[],[f96,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f104,plain,
    ( spl4_3
    | spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f92,f102,f98,f94])).

fof(f92,plain,(
    ! [X0] :
      ( u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f91,f43])).

fof(f43,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f89,f59])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f87,f57])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_tsep_1(X0,X1,X2))
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f67,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2)))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f76,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f66,f73,f69])).

fof(f66,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X5] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:18:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (25038)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.49  % (25030)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (25015)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (25025)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (25041)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (25035)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (25027)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.53  % (25031)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.53  % (25034)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.53  % (25017)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.53  % (25013)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.53  % (25018)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.53  % (25014)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.53  % (25035)Refutation not found, incomplete strategy% (25035)------------------------------
% 1.35/0.53  % (25035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (25035)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (25035)Memory used [KB]: 10746
% 1.35/0.53  % (25035)Time elapsed: 0.079 s
% 1.35/0.53  % (25035)------------------------------
% 1.35/0.53  % (25035)------------------------------
% 1.35/0.54  % (25019)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.54  % (25026)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.54  % (25025)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f187,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(avatar_sat_refutation,[],[f76,f104,f106,f115,f133,f136,f138,f154,f168,f170,f172,f176,f178,f183,f186])).
% 1.35/0.54  fof(f186,plain,(
% 1.35/0.54    spl4_1 | ~spl4_14),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f185])).
% 1.35/0.54  fof(f185,plain,(
% 1.35/0.54    $false | (spl4_1 | ~spl4_14)),
% 1.35/0.54    inference(resolution,[],[f184,f44])).
% 1.35/0.54  fof(f44,plain,(
% 1.35/0.54    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f33,plain,(
% 1.35/0.54    ((((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f32,f31,f30,f29])).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    ? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) => ((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f16,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f15])).
% 1.35/0.54  fof(f15,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f14])).
% 1.35/0.54  fof(f14,plain,(
% 1.35/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.35/0.54    inference(rectify,[],[f13])).
% 1.35/0.54  fof(f13,negated_conjecture,(
% 1.35/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.35/0.54    inference(negated_conjecture,[],[f12])).
% 1.35/0.54  fof(f12,conjecture,(
% 1.35/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).
% 1.35/0.54  fof(f184,plain,(
% 1.35/0.54    ~m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | (spl4_1 | ~spl4_14)),
% 1.35/0.54    inference(resolution,[],[f175,f71])).
% 1.35/0.54  fof(f71,plain,(
% 1.35/0.54    ~m1_subset_1(sK3,u1_struct_0(sK1)) | spl4_1),
% 1.35/0.54    inference(avatar_component_clause,[],[f69])).
% 1.35/0.54  fof(f69,plain,(
% 1.35/0.54    spl4_1 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.35/0.54  fof(f175,plain,(
% 1.35/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) ) | ~spl4_14),
% 1.35/0.54    inference(avatar_component_clause,[],[f174])).
% 1.35/0.54  fof(f174,plain,(
% 1.35/0.54    spl4_14 <=> ! [X0] : (m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.35/0.54  fof(f183,plain,(
% 1.35/0.54    spl4_2 | ~spl4_12),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f182])).
% 1.35/0.54  fof(f182,plain,(
% 1.35/0.54    $false | (spl4_2 | ~spl4_12)),
% 1.35/0.54    inference(resolution,[],[f181,f44])).
% 1.35/0.54  fof(f181,plain,(
% 1.35/0.54    ~m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | (spl4_2 | ~spl4_12)),
% 1.35/0.54    inference(resolution,[],[f153,f75])).
% 1.35/0.54  fof(f75,plain,(
% 1.35/0.54    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl4_2),
% 1.35/0.54    inference(avatar_component_clause,[],[f73])).
% 1.35/0.54  fof(f73,plain,(
% 1.35/0.54    spl4_2 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.35/0.54  fof(f153,plain,(
% 1.35/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) ) | ~spl4_12),
% 1.35/0.54    inference(avatar_component_clause,[],[f152])).
% 1.35/0.54  fof(f152,plain,(
% 1.35/0.54    spl4_12 <=> ! [X0] : (m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.35/0.54  fof(f178,plain,(
% 1.35/0.54    spl4_9 | ~spl4_8 | spl4_3 | ~spl4_7 | spl4_4 | ~spl4_13 | ~spl4_10),
% 1.35/0.54    inference(avatar_split_clause,[],[f177,f144,f165,f98,f122,f94,f126,f130])).
% 1.35/0.54  fof(f130,plain,(
% 1.35/0.54    spl4_9 <=> v2_struct_0(sK0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.35/0.54  fof(f126,plain,(
% 1.35/0.54    spl4_8 <=> l1_pre_topc(sK0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.35/0.54  fof(f94,plain,(
% 1.35/0.54    spl4_3 <=> v2_struct_0(sK1)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.35/0.54  fof(f122,plain,(
% 1.35/0.54    spl4_7 <=> m1_pre_topc(sK1,sK0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.35/0.54  fof(f98,plain,(
% 1.35/0.54    spl4_4 <=> v2_struct_0(sK2)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.35/0.54  fof(f165,plain,(
% 1.35/0.54    spl4_13 <=> m1_pre_topc(sK2,sK0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.35/0.54  fof(f144,plain,(
% 1.35/0.54    spl4_10 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.35/0.54  fof(f177,plain,(
% 1.35/0.54    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_10),
% 1.35/0.54    inference(resolution,[],[f146,f57])).
% 1.35/0.54  fof(f57,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f26])).
% 1.35/0.54  fof(f26,plain,(
% 1.35/0.54    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f25])).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f11])).
% 1.35/0.54  fof(f11,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.35/0.54  fof(f146,plain,(
% 1.35/0.54    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_10),
% 1.35/0.54    inference(avatar_component_clause,[],[f144])).
% 1.35/0.54  fof(f176,plain,(
% 1.35/0.54    spl4_10 | ~spl4_11 | spl4_14 | ~spl4_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f161,f118,f174,f148,f144])).
% 1.35/0.54  fof(f148,plain,(
% 1.35/0.54    spl4_11 <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.35/0.54  fof(f118,plain,(
% 1.35/0.54    spl4_6 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.35/0.54  fof(f161,plain,(
% 1.35/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) | ~spl4_6),
% 1.35/0.54    inference(resolution,[],[f141,f84])).
% 1.35/0.54  fof(f84,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X0),X1) | m1_subset_1(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(resolution,[],[f83,f48])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f20])).
% 1.35/0.54  fof(f20,plain,(
% 1.35/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f19])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f9])).
% 1.35/0.54  fof(f9,axiom,(
% 1.35/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.35/0.54  fof(f83,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~r1_tarski(X2,X1) | m1_subset_1(X0,X1) | ~m1_subset_1(X0,X2)) )),
% 1.35/0.54    inference(resolution,[],[f82,f54])).
% 1.35/0.54  fof(f54,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.35/0.54    inference(flattening,[],[f23])).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.35/0.54  % (25016)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  fof(f82,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | m1_subset_1(X0,X1) | ~r1_tarski(X2,X1)) )),
% 1.35/0.54    inference(resolution,[],[f60,f56])).
% 1.35/0.54  fof(f56,plain,(
% 1.35/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f35])).
% 1.35/0.54  fof(f35,plain,(
% 1.35/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.35/0.54    inference(nnf_transformation,[],[f5])).
% 1.35/0.54  fof(f5,axiom,(
% 1.35/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.35/0.54  fof(f60,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f28])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.35/0.54    inference(flattening,[],[f27])).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.35/0.54    inference(ennf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.35/0.54  fof(f141,plain,(
% 1.35/0.54    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~spl4_6),
% 1.35/0.54    inference(superposition,[],[f63,f120])).
% 1.35/0.54  fof(f120,plain,(
% 1.35/0.54    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl4_6),
% 1.35/0.54    inference(avatar_component_clause,[],[f118])).
% 1.35/0.54  fof(f63,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f51,f53])).
% 1.35/0.54  fof(f53,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.35/0.54  fof(f51,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.35/0.54  fof(f172,plain,(
% 1.35/0.54    ~spl4_9),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f171])).
% 1.35/0.54  fof(f171,plain,(
% 1.35/0.54    $false | ~spl4_9),
% 1.35/0.54    inference(resolution,[],[f132,f36])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ~v2_struct_0(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f132,plain,(
% 1.35/0.54    v2_struct_0(sK0) | ~spl4_9),
% 1.35/0.54    inference(avatar_component_clause,[],[f130])).
% 1.35/0.54  fof(f170,plain,(
% 1.35/0.54    spl4_13),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f169])).
% 1.35/0.54  fof(f169,plain,(
% 1.35/0.54    $false | spl4_13),
% 1.35/0.54    inference(resolution,[],[f167,f42])).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    m1_pre_topc(sK2,sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f167,plain,(
% 1.35/0.54    ~m1_pre_topc(sK2,sK0) | spl4_13),
% 1.35/0.54    inference(avatar_component_clause,[],[f165])).
% 1.35/0.54  fof(f168,plain,(
% 1.35/0.54    spl4_9 | spl4_3 | ~spl4_7 | spl4_4 | ~spl4_13 | ~spl4_8 | spl4_11),
% 1.35/0.54    inference(avatar_split_clause,[],[f163,f148,f126,f165,f98,f122,f94,f130])).
% 1.35/0.54  fof(f163,plain,(
% 1.35/0.54    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | spl4_11),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f162])).
% 1.35/0.54  fof(f162,plain,(
% 1.35/0.54    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_11),
% 1.35/0.54    inference(resolution,[],[f160,f59])).
% 1.35/0.54  fof(f59,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f26])).
% 1.35/0.54  fof(f160,plain,(
% 1.35/0.54    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0)) ) | spl4_11),
% 1.35/0.54    inference(resolution,[],[f159,f47])).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f18])).
% 1.35/0.54  fof(f18,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,axiom,(
% 1.35/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.35/0.54  fof(f159,plain,(
% 1.35/0.54    ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | spl4_11),
% 1.35/0.54    inference(resolution,[],[f150,f46])).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f17])).
% 1.35/0.54  fof(f17,plain,(
% 1.35/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f7])).
% 1.35/0.54  fof(f7,axiom,(
% 1.35/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.35/0.54  fof(f150,plain,(
% 1.35/0.54    ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | spl4_11),
% 1.35/0.54    inference(avatar_component_clause,[],[f148])).
% 1.35/0.54  fof(f154,plain,(
% 1.35/0.54    spl4_10 | ~spl4_11 | spl4_12 | ~spl4_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f142,f118,f152,f148,f144])).
% 1.35/0.54  fof(f142,plain,(
% 1.35/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) | ~spl4_6),
% 1.35/0.54    inference(resolution,[],[f140,f84])).
% 1.35/0.54  fof(f140,plain,(
% 1.35/0.54    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) | ~spl4_6),
% 1.35/0.54    inference(superposition,[],[f78,f120])).
% 1.35/0.54  fof(f78,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 1.35/0.54    inference(superposition,[],[f63,f64])).
% 1.35/0.54  fof(f64,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f52,f53,f53])).
% 1.35/0.54  fof(f52,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f1])).
% 1.35/0.54  fof(f1,axiom,(
% 1.35/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.35/0.54  fof(f138,plain,(
% 1.35/0.54    spl4_7),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f137])).
% 1.35/0.54  fof(f137,plain,(
% 1.35/0.54    $false | spl4_7),
% 1.35/0.54    inference(resolution,[],[f124,f40])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    m1_pre_topc(sK1,sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f124,plain,(
% 1.35/0.54    ~m1_pre_topc(sK1,sK0) | spl4_7),
% 1.35/0.54    inference(avatar_component_clause,[],[f122])).
% 1.35/0.54  fof(f136,plain,(
% 1.35/0.54    spl4_8),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f134])).
% 1.35/0.54  fof(f134,plain,(
% 1.35/0.54    $false | spl4_8),
% 1.35/0.54    inference(resolution,[],[f128,f38])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    l1_pre_topc(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f128,plain,(
% 1.35/0.54    ~l1_pre_topc(sK0) | spl4_8),
% 1.35/0.54    inference(avatar_component_clause,[],[f126])).
% 1.35/0.54  fof(f133,plain,(
% 1.35/0.54    spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9 | ~spl4_5),
% 1.35/0.54    inference(avatar_split_clause,[],[f116,f102,f130,f126,f122,f118])).
% 1.35/0.54  fof(f102,plain,(
% 1.35/0.54    spl4_5 <=> ! [X0] : (u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.35/0.54  fof(f116,plain,(
% 1.35/0.54    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl4_5),
% 1.35/0.54    inference(resolution,[],[f103,f42])).
% 1.35/0.54  fof(f103,plain,(
% 1.35/0.54    ( ! [X0] : (~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))) ) | ~spl4_5),
% 1.35/0.54    inference(avatar_component_clause,[],[f102])).
% 1.35/0.54  fof(f115,plain,(
% 1.35/0.54    ~spl4_4),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f114])).
% 1.35/0.54  fof(f114,plain,(
% 1.35/0.54    $false | ~spl4_4),
% 1.35/0.54    inference(resolution,[],[f100,f41])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ~v2_struct_0(sK2)),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f100,plain,(
% 1.35/0.54    v2_struct_0(sK2) | ~spl4_4),
% 1.35/0.54    inference(avatar_component_clause,[],[f98])).
% 1.35/0.54  fof(f106,plain,(
% 1.35/0.54    ~spl4_3),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f105])).
% 1.35/0.54  fof(f105,plain,(
% 1.35/0.54    $false | ~spl4_3),
% 1.35/0.54    inference(resolution,[],[f96,f39])).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    ~v2_struct_0(sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f96,plain,(
% 1.35/0.54    v2_struct_0(sK1) | ~spl4_3),
% 1.35/0.54    inference(avatar_component_clause,[],[f94])).
% 1.35/0.54  fof(f104,plain,(
% 1.35/0.54    spl4_3 | spl4_4 | spl4_5),
% 1.35/0.54    inference(avatar_split_clause,[],[f92,f102,f98,f94])).
% 1.35/0.54  fof(f92,plain,(
% 1.35/0.54    ( ! [X0] : (u1_struct_0(k2_tsep_1(X0,sK1,sK2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(resolution,[],[f91,f43])).
% 1.35/0.54  fof(f43,plain,(
% 1.35/0.54    ~r1_tsep_1(sK1,sK2)),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  fof(f91,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f90])).
% 1.35/0.54  fof(f90,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(resolution,[],[f89,f59])).
% 1.35/0.54  fof(f89,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f88])).
% 1.35/0.54  fof(f88,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(resolution,[],[f87,f57])).
% 1.35/0.54  fof(f87,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (v2_struct_0(k2_tsep_1(X0,X1,X2)) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f86])).
% 1.35/0.54  fof(f86,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(resolution,[],[f67,f58])).
% 1.35/0.54  fof(f58,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f26])).
% 1.35/0.54  fof(f67,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(equality_resolution,[],[f62])).
% 1.35/0.54  fof(f62,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X2))) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f49,f53])).
% 1.35/0.54  fof(f49,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f34])).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(nnf_transformation,[],[f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f21])).
% 1.35/0.54  fof(f21,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.35/0.54  fof(f76,plain,(
% 1.35/0.54    ~spl4_1 | ~spl4_2),
% 1.35/0.54    inference(avatar_split_clause,[],[f66,f73,f69])).
% 1.35/0.54  fof(f66,plain,(
% 1.35/0.54    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.35/0.54    inference(equality_resolution,[],[f65])).
% 1.35/0.54  fof(f65,plain,(
% 1.35/0.54    ( ! [X5] : (~m1_subset_1(sK3,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.35/0.54    inference(equality_resolution,[],[f45])).
% 1.35/0.54  fof(f45,plain,(
% 1.35/0.54    ( ! [X4,X5] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f33])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (25025)------------------------------
% 1.35/0.54  % (25025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (25025)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (25025)Memory used [KB]: 6396
% 1.35/0.54  % (25025)Time elapsed: 0.113 s
% 1.35/0.54  % (25025)------------------------------
% 1.35/0.54  % (25025)------------------------------
% 1.35/0.54  % (25012)Success in time 0.184 s
%------------------------------------------------------------------------------
