%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:11 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 534 expanded)
%              Number of leaves         :   44 ( 192 expanded)
%              Depth                    :   17
%              Number of atoms          :  537 (4380 expanded)
%              Number of equality atoms :   67 ( 446 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f131,f133,f149,f159,f161,f200,f208,f249,f251,f253,f260,f290,f299,f301])).

fof(f301,plain,(
    ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl4_15 ),
    inference(resolution,[],[f285,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f285,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl4_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f299,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f296,f287,f122,f118,f283])).

fof(f118,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f122,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f287,plain,
    ( spl4_16
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f296,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_16 ),
    inference(resolution,[],[f291,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f291,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl4_16 ),
    inference(resolution,[],[f289,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f77,f103])).

fof(f103,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f65,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f289,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f287])).

fof(f290,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_2
    | spl4_16
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f274,f189,f287,f122,f118,f283])).

fof(f189,plain,
    ( spl4_7
  <=> u1_struct_0(sK0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f274,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7 ),
    inference(superposition,[],[f79,f191])).

fof(f191,plain,
    ( u1_struct_0(sK0) = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f189])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f260,plain,(
    ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl4_14 ),
    inference(resolution,[],[f258,f104])).

fof(f104,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f67,f65])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f258,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_14 ),
    inference(resolution,[],[f248,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f248,plain,
    ( r2_hidden(u1_struct_0(sK0),sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl4_14
  <=> r2_hidden(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f253,plain,
    ( ~ spl4_2
    | ~ spl4_6
    | spl4_13 ),
    inference(avatar_split_clause,[],[f252,f242,f156,f122])).

fof(f156,plain,
    ( spl4_6
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f242,plain,
    ( spl4_13
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f252,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_13 ),
    inference(resolution,[],[f244,f232])).

fof(f232,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ v4_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f178,f105])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f69,f65])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f178,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v4_pre_topc(sK2,X5)
      | v3_pre_topc(u1_struct_0(X5),X5)
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f75,f169])).

fof(f169,plain,(
    ! [X1] : k3_subset_1(X1,sK2) = X1 ),
    inference(forward_demodulation,[],[f168,f107])).

fof(f107,plain,(
    ! [X0] : k5_xboole_0(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f71,f65])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f168,plain,(
    ! [X1] : k3_subset_1(X1,sK2) = k5_xboole_0(X1,sK2) ),
    inference(forward_demodulation,[],[f166,f106])).

fof(f106,plain,(
    ! [X0] : sK2 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) ),
    inference(definition_unfolding,[],[f70,f65,f101,f65])).

fof(f101,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f85,f100])).

fof(f100,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f86,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f90,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f92,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f93,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f94,f95])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f90,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f86,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f166,plain,(
    ! [X1] : k3_subset_1(X1,sK2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2))) ),
    inference(resolution,[],[f109,f105])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f88,f102])).

fof(f102,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f87,f101])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f244,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f242])).

fof(f251,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f240,f110])).

fof(f110,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f72,f68])).

fof(f68,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f240,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl4_12
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f249,plain,
    ( ~ spl4_12
    | ~ spl4_13
    | ~ spl4_3
    | spl4_14
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f209,f197,f246,f126,f242,f238])).

fof(f126,plain,
    ( spl4_3
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f197,plain,
    ( spl4_9
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f209,plain,
    ( r2_hidden(u1_struct_0(sK0),sK2)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(resolution,[],[f199,f64])).

fof(f64,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f199,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f197])).

fof(f208,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl4_8 ),
    inference(resolution,[],[f206,f104])).

fof(f206,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f195,f89])).

fof(f195,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_8
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f200,plain,
    ( spl4_7
    | spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f182,f197,f193,f189])).

fof(f182,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,sK2)
    | u1_struct_0(sK0) = sK2 ),
    inference(resolution,[],[f173,f59])).

fof(f59,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,sK2)
      | sK2 = X1 ) ),
    inference(backward_demodulation,[],[f134,f169])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_subset_1(X1,sK2))
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,sK2)
      | sK2 = X1 ) ),
    inference(resolution,[],[f108,f105])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | r2_hidden(X2,k3_subset_1(X0,X1))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f78,f65])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f161,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f154,f105])).

fof(f154,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f159,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f150,f147,f156,f152])).

fof(f147,plain,
    ( spl4_4
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f150,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f148,f103])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f145,f147,f118])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f84,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f133,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f124,f58])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f131,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f120,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f120,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f129,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f116,f126,f122,f118])).

fof(f116,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f83,f112])).

fof(f112,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f111,f58])).

fof(f111,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f73,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f83,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n003.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 20:27:27 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.11/0.37  % (21243)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.11/0.37  % (21247)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.11/0.38  % (21241)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.11/0.38  % (21245)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.11/0.38  % (21256)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.11/0.38  % (21243)Refutation found. Thanks to Tanya!
% 0.11/0.38  % SZS status Theorem for theBenchmark
% 0.11/0.38  % SZS output start Proof for theBenchmark
% 0.11/0.38  fof(f302,plain,(
% 0.11/0.38    $false),
% 0.11/0.38    inference(avatar_sat_refutation,[],[f129,f131,f133,f149,f159,f161,f200,f208,f249,f251,f253,f260,f290,f299,f301])).
% 0.11/0.38  fof(f301,plain,(
% 0.11/0.38    ~spl4_15),
% 0.11/0.38    inference(avatar_contradiction_clause,[],[f300])).
% 0.11/0.39  fof(f300,plain,(
% 0.11/0.39    $false | ~spl4_15),
% 0.11/0.39    inference(resolution,[],[f285,f56])).
% 0.11/0.39  fof(f56,plain,(
% 0.11/0.39    ~v2_struct_0(sK0)),
% 0.11/0.39    inference(cnf_transformation,[],[f52])).
% 0.11/0.39  fof(f52,plain,(
% 0.11/0.39    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.11/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).
% 0.11/0.39  fof(f49,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f50,plain,(
% 0.11/0.39    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f51,plain,(
% 0.11/0.39    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f48,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.11/0.39    inference(flattening,[],[f47])).
% 0.11/0.39  fof(f47,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.11/0.39    inference(nnf_transformation,[],[f30])).
% 0.11/0.39  fof(f30,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.11/0.39    inference(flattening,[],[f29])).
% 0.11/0.39  fof(f29,plain,(
% 0.11/0.39    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.11/0.39    inference(ennf_transformation,[],[f28])).
% 0.11/0.39  fof(f28,negated_conjecture,(
% 0.11/0.39    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.11/0.39    inference(negated_conjecture,[],[f27])).
% 0.11/0.39  fof(f27,conjecture,(
% 0.11/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.11/0.39  fof(f285,plain,(
% 0.11/0.39    v2_struct_0(sK0) | ~spl4_15),
% 0.11/0.39    inference(avatar_component_clause,[],[f283])).
% 0.11/0.39  fof(f283,plain,(
% 0.11/0.39    spl4_15 <=> v2_struct_0(sK0)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.11/0.39  fof(f299,plain,(
% 0.11/0.39    spl4_15 | ~spl4_1 | ~spl4_2 | ~spl4_16),
% 0.11/0.39    inference(avatar_split_clause,[],[f296,f287,f122,f118,f283])).
% 0.11/0.39  fof(f118,plain,(
% 0.11/0.39    spl4_1 <=> v2_pre_topc(sK0)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.11/0.39  fof(f122,plain,(
% 0.11/0.39    spl4_2 <=> l1_pre_topc(sK0)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.11/0.39  fof(f287,plain,(
% 0.11/0.39    spl4_16 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.11/0.39  fof(f296,plain,(
% 0.11/0.39    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_16),
% 0.11/0.39    inference(resolution,[],[f291,f80])).
% 0.11/0.39  fof(f80,plain,(
% 0.11/0.39    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f55])).
% 0.11/0.39  fof(f55,plain,(
% 0.11/0.39    ! [X0] : ((v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.11/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f54])).
% 0.11/0.39  fof(f54,plain,(
% 0.11/0.39    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.11/0.39    introduced(choice_axiom,[])).
% 0.11/0.39  fof(f38,plain,(
% 0.11/0.39    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.11/0.39    inference(flattening,[],[f37])).
% 0.11/0.39  fof(f37,plain,(
% 0.11/0.39    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.11/0.39    inference(ennf_transformation,[],[f25])).
% 0.11/0.39  fof(f25,axiom,(
% 0.11/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.11/0.39  fof(f291,plain,(
% 0.11/0.39    v1_xboole_0(sK3(sK0)) | ~spl4_16),
% 0.11/0.39    inference(resolution,[],[f289,f113])).
% 0.11/0.39  fof(f113,plain,(
% 0.11/0.39    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_xboole_0(X0)) )),
% 0.11/0.39    inference(resolution,[],[f77,f103])).
% 0.11/0.39  fof(f103,plain,(
% 0.11/0.39    v1_xboole_0(sK2)),
% 0.11/0.39    inference(definition_unfolding,[],[f66,f65])).
% 0.11/0.39  fof(f65,plain,(
% 0.11/0.39    k1_xboole_0 = sK2),
% 0.11/0.39    inference(cnf_transformation,[],[f52])).
% 0.11/0.39  fof(f66,plain,(
% 0.11/0.39    v1_xboole_0(k1_xboole_0)),
% 0.11/0.39    inference(cnf_transformation,[],[f1])).
% 0.11/0.39  fof(f1,axiom,(
% 0.11/0.39    v1_xboole_0(k1_xboole_0)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.11/0.39  fof(f77,plain,(
% 0.11/0.39    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f34])).
% 0.11/0.39  fof(f34,plain,(
% 0.11/0.39    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.11/0.39    inference(ennf_transformation,[],[f17])).
% 0.11/0.39  fof(f17,axiom,(
% 0.11/0.39    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.11/0.39  fof(f289,plain,(
% 0.11/0.39    m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) | ~spl4_16),
% 0.11/0.39    inference(avatar_component_clause,[],[f287])).
% 0.11/0.39  fof(f290,plain,(
% 0.11/0.39    spl4_15 | ~spl4_1 | ~spl4_2 | spl4_16 | ~spl4_7),
% 0.11/0.39    inference(avatar_split_clause,[],[f274,f189,f287,f122,f118,f283])).
% 0.11/0.39  fof(f189,plain,(
% 0.11/0.39    spl4_7 <=> u1_struct_0(sK0) = sK2),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.11/0.39  fof(f274,plain,(
% 0.11/0.39    m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_7),
% 0.11/0.39    inference(superposition,[],[f79,f191])).
% 0.11/0.39  fof(f191,plain,(
% 0.11/0.39    u1_struct_0(sK0) = sK2 | ~spl4_7),
% 0.11/0.39    inference(avatar_component_clause,[],[f189])).
% 0.11/0.39  fof(f79,plain,(
% 0.11/0.39    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f55])).
% 0.11/0.39  fof(f260,plain,(
% 0.11/0.39    ~spl4_14),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f259])).
% 0.11/0.39  fof(f259,plain,(
% 0.11/0.39    $false | ~spl4_14),
% 0.11/0.39    inference(resolution,[],[f258,f104])).
% 0.11/0.39  fof(f104,plain,(
% 0.11/0.39    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f67,f65])).
% 0.11/0.39  fof(f67,plain,(
% 0.11/0.39    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f4])).
% 0.11/0.39  fof(f4,axiom,(
% 0.11/0.39    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.11/0.39  fof(f258,plain,(
% 0.11/0.39    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~spl4_14),
% 0.11/0.39    inference(resolution,[],[f248,f89])).
% 0.11/0.39  fof(f89,plain,(
% 0.11/0.39    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f44])).
% 0.11/0.39  fof(f44,plain,(
% 0.11/0.39    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.11/0.39    inference(ennf_transformation,[],[f20])).
% 0.11/0.39  fof(f20,axiom,(
% 0.11/0.39    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.11/0.39  fof(f248,plain,(
% 0.11/0.39    r2_hidden(u1_struct_0(sK0),sK2) | ~spl4_14),
% 0.11/0.39    inference(avatar_component_clause,[],[f246])).
% 0.11/0.39  fof(f246,plain,(
% 0.11/0.39    spl4_14 <=> r2_hidden(u1_struct_0(sK0),sK2)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.11/0.39  fof(f253,plain,(
% 0.11/0.39    ~spl4_2 | ~spl4_6 | spl4_13),
% 0.11/0.39    inference(avatar_split_clause,[],[f252,f242,f156,f122])).
% 0.11/0.39  fof(f156,plain,(
% 0.11/0.39    spl4_6 <=> v4_pre_topc(sK2,sK0)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.11/0.39  fof(f242,plain,(
% 0.11/0.39    spl4_13 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.11/0.39  fof(f252,plain,(
% 0.11/0.39    ~v4_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | spl4_13),
% 0.11/0.39    inference(resolution,[],[f244,f232])).
% 0.11/0.39  fof(f232,plain,(
% 0.11/0.39    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~v4_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.11/0.39    inference(resolution,[],[f178,f105])).
% 0.11/0.39  fof(f105,plain,(
% 0.11/0.39    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.11/0.39    inference(definition_unfolding,[],[f69,f65])).
% 0.11/0.39  fof(f69,plain,(
% 0.11/0.39    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f15])).
% 0.11/0.39  fof(f15,axiom,(
% 0.11/0.39    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.11/0.39  fof(f178,plain,(
% 0.11/0.39    ( ! [X5] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X5))) | ~v4_pre_topc(sK2,X5) | v3_pre_topc(u1_struct_0(X5),X5) | ~l1_pre_topc(X5)) )),
% 0.11/0.39    inference(superposition,[],[f75,f169])).
% 0.11/0.39  fof(f169,plain,(
% 0.11/0.39    ( ! [X1] : (k3_subset_1(X1,sK2) = X1) )),
% 0.11/0.39    inference(forward_demodulation,[],[f168,f107])).
% 0.11/0.39  fof(f107,plain,(
% 0.11/0.39    ( ! [X0] : (k5_xboole_0(X0,sK2) = X0) )),
% 0.11/0.39    inference(definition_unfolding,[],[f71,f65])).
% 0.11/0.39  fof(f71,plain,(
% 0.11/0.39    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.11/0.39    inference(cnf_transformation,[],[f5])).
% 0.11/0.39  fof(f5,axiom,(
% 0.11/0.39    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.11/0.39  fof(f168,plain,(
% 0.11/0.39    ( ! [X1] : (k3_subset_1(X1,sK2) = k5_xboole_0(X1,sK2)) )),
% 0.11/0.39    inference(forward_demodulation,[],[f166,f106])).
% 0.11/0.39  fof(f106,plain,(
% 0.11/0.39    ( ! [X0] : (sK2 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))) )),
% 0.11/0.39    inference(definition_unfolding,[],[f70,f65,f101,f65])).
% 0.11/0.39  fof(f101,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.11/0.39    inference(definition_unfolding,[],[f85,f100])).
% 0.11/0.39  fof(f100,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f86,f99])).
% 0.11/0.39  fof(f99,plain,(
% 0.11/0.39    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f90,f98])).
% 0.11/0.39  fof(f98,plain,(
% 0.11/0.39    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f92,f97])).
% 0.11/0.39  fof(f97,plain,(
% 0.11/0.39    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f93,f96])).
% 0.11/0.39  fof(f96,plain,(
% 0.11/0.39    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f94,f95])).
% 0.11/0.39  fof(f95,plain,(
% 0.11/0.39    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f11])).
% 0.11/0.39  fof(f11,axiom,(
% 0.11/0.39    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.11/0.39  fof(f94,plain,(
% 0.11/0.39    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f10])).
% 0.11/0.39  fof(f10,axiom,(
% 0.11/0.39    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.11/0.39  fof(f93,plain,(
% 0.11/0.39    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f9])).
% 0.11/0.39  fof(f9,axiom,(
% 0.11/0.39    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.11/0.39  fof(f92,plain,(
% 0.11/0.39    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f8])).
% 0.11/0.39  fof(f8,axiom,(
% 0.11/0.39    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.11/0.39  fof(f90,plain,(
% 0.11/0.39    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f7])).
% 0.11/0.39  fof(f7,axiom,(
% 0.11/0.39    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.11/0.39  fof(f86,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f6])).
% 0.11/0.39  fof(f6,axiom,(
% 0.11/0.39    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.11/0.39  fof(f85,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f18])).
% 0.11/0.39  fof(f18,axiom,(
% 0.11/0.39    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.11/0.39  fof(f70,plain,(
% 0.11/0.39    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f3])).
% 0.11/0.39  fof(f3,axiom,(
% 0.11/0.39    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.11/0.39  fof(f166,plain,(
% 0.11/0.39    ( ! [X1] : (k3_subset_1(X1,sK2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2)))) )),
% 0.11/0.39    inference(resolution,[],[f109,f105])).
% 0.11/0.39  fof(f109,plain,(
% 0.11/0.39    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.11/0.39    inference(definition_unfolding,[],[f88,f102])).
% 0.11/0.39  fof(f102,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.11/0.39    inference(definition_unfolding,[],[f87,f101])).
% 0.11/0.39  fof(f87,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f2])).
% 0.11/0.39  fof(f2,axiom,(
% 0.11/0.39    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.11/0.39  fof(f88,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f43])).
% 0.11/0.39  fof(f43,plain,(
% 0.11/0.39    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.11/0.39    inference(ennf_transformation,[],[f13])).
% 0.11/0.39  fof(f13,axiom,(
% 0.11/0.39    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.11/0.39  fof(f75,plain,(
% 0.11/0.39    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f53])).
% 0.11/0.39  fof(f53,plain,(
% 0.11/0.39    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.11/0.39    inference(nnf_transformation,[],[f33])).
% 0.11/0.39  fof(f33,plain,(
% 0.11/0.39    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.11/0.39    inference(ennf_transformation,[],[f26])).
% 0.11/0.39  fof(f26,axiom,(
% 0.11/0.39    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.11/0.39  fof(f244,plain,(
% 0.11/0.39    ~v3_pre_topc(u1_struct_0(sK0),sK0) | spl4_13),
% 0.11/0.39    inference(avatar_component_clause,[],[f242])).
% 0.11/0.39  fof(f251,plain,(
% 0.11/0.39    spl4_12),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f250])).
% 0.11/0.39  fof(f250,plain,(
% 0.11/0.39    $false | spl4_12),
% 0.11/0.39    inference(resolution,[],[f240,f110])).
% 0.11/0.39  fof(f110,plain,(
% 0.11/0.39    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.11/0.39    inference(forward_demodulation,[],[f72,f68])).
% 0.11/0.39  fof(f68,plain,(
% 0.11/0.39    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.11/0.39    inference(cnf_transformation,[],[f12])).
% 0.11/0.39  fof(f12,axiom,(
% 0.11/0.39    ! [X0] : k2_subset_1(X0) = X0),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.11/0.39  fof(f72,plain,(
% 0.11/0.39    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f14])).
% 0.11/0.39  fof(f14,axiom,(
% 0.11/0.39    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.11/0.39  fof(f240,plain,(
% 0.11/0.39    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_12),
% 0.11/0.39    inference(avatar_component_clause,[],[f238])).
% 0.11/0.39  fof(f238,plain,(
% 0.11/0.39    spl4_12 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.11/0.39  fof(f249,plain,(
% 0.11/0.39    ~spl4_12 | ~spl4_13 | ~spl4_3 | spl4_14 | ~spl4_9),
% 0.11/0.39    inference(avatar_split_clause,[],[f209,f197,f246,f126,f242,f238])).
% 0.11/0.39  fof(f126,plain,(
% 0.11/0.39    spl4_3 <=> v4_pre_topc(u1_struct_0(sK0),sK0)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.11/0.39  fof(f197,plain,(
% 0.11/0.39    spl4_9 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.11/0.39  fof(f209,plain,(
% 0.11/0.39    r2_hidden(u1_struct_0(sK0),sK2) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_9),
% 0.11/0.39    inference(resolution,[],[f199,f64])).
% 0.11/0.39  fof(f64,plain,(
% 0.11/0.39    ( ! [X3] : (~r2_hidden(sK1,X3) | r2_hidden(X3,sK2) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f52])).
% 0.11/0.39  fof(f199,plain,(
% 0.11/0.39    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl4_9),
% 0.11/0.39    inference(avatar_component_clause,[],[f197])).
% 0.11/0.39  fof(f208,plain,(
% 0.11/0.39    ~spl4_8),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f207])).
% 0.11/0.39  fof(f207,plain,(
% 0.11/0.39    $false | ~spl4_8),
% 0.11/0.39    inference(resolution,[],[f206,f104])).
% 0.11/0.39  fof(f206,plain,(
% 0.11/0.39    ~r1_tarski(sK2,sK1) | ~spl4_8),
% 0.11/0.39    inference(resolution,[],[f195,f89])).
% 0.11/0.39  fof(f195,plain,(
% 0.11/0.39    r2_hidden(sK1,sK2) | ~spl4_8),
% 0.11/0.39    inference(avatar_component_clause,[],[f193])).
% 0.11/0.39  fof(f193,plain,(
% 0.11/0.39    spl4_8 <=> r2_hidden(sK1,sK2)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.11/0.39  fof(f200,plain,(
% 0.11/0.39    spl4_7 | spl4_8 | spl4_9),
% 0.11/0.39    inference(avatar_split_clause,[],[f182,f197,f193,f189])).
% 0.11/0.39  fof(f182,plain,(
% 0.11/0.39    r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(sK1,sK2) | u1_struct_0(sK0) = sK2),
% 0.11/0.39    inference(resolution,[],[f173,f59])).
% 0.11/0.39  fof(f59,plain,(
% 0.11/0.39    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.11/0.39    inference(cnf_transformation,[],[f52])).
% 0.11/0.39  fof(f173,plain,(
% 0.11/0.39    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | r2_hidden(X0,sK2) | sK2 = X1) )),
% 0.11/0.39    inference(backward_demodulation,[],[f134,f169])).
% 0.11/0.39  fof(f134,plain,(
% 0.11/0.39    ( ! [X0,X1] : (r2_hidden(X0,k3_subset_1(X1,sK2)) | ~m1_subset_1(X0,X1) | r2_hidden(X0,sK2) | sK2 = X1) )),
% 0.11/0.39    inference(resolution,[],[f108,f105])).
% 0.11/0.39  fof(f108,plain,(
% 0.11/0.39    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | r2_hidden(X2,k3_subset_1(X0,X1)) | sK2 = X0) )),
% 0.11/0.39    inference(definition_unfolding,[],[f78,f65])).
% 0.11/0.39  fof(f78,plain,(
% 0.11/0.39    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.11/0.39    inference(cnf_transformation,[],[f36])).
% 0.11/0.39  fof(f36,plain,(
% 0.11/0.39    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.11/0.39    inference(flattening,[],[f35])).
% 0.11/0.39  fof(f35,plain,(
% 0.11/0.39    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.11/0.39    inference(ennf_transformation,[],[f16])).
% 0.11/0.39  fof(f16,axiom,(
% 0.11/0.39    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 0.11/0.39  fof(f161,plain,(
% 0.11/0.39    spl4_5),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f160])).
% 0.11/0.39  fof(f160,plain,(
% 0.11/0.39    $false | spl4_5),
% 0.11/0.39    inference(resolution,[],[f154,f105])).
% 0.11/0.39  fof(f154,plain,(
% 0.11/0.39    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_5),
% 0.11/0.39    inference(avatar_component_clause,[],[f152])).
% 0.11/0.39  fof(f152,plain,(
% 0.11/0.39    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.11/0.39  fof(f159,plain,(
% 0.11/0.39    ~spl4_5 | spl4_6 | ~spl4_4),
% 0.11/0.39    inference(avatar_split_clause,[],[f150,f147,f156,f152])).
% 0.11/0.39  fof(f147,plain,(
% 0.11/0.39    spl4_4 <=> ! [X0] : (~v1_xboole_0(X0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.11/0.39  fof(f150,plain,(
% 0.11/0.39    v4_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.11/0.39    inference(resolution,[],[f148,f103])).
% 0.11/0.39  fof(f148,plain,(
% 0.11/0.39    ( ! [X0] : (~v1_xboole_0(X0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_4),
% 0.11/0.39    inference(avatar_component_clause,[],[f147])).
% 0.11/0.39  fof(f149,plain,(
% 0.11/0.39    ~spl4_1 | spl4_4),
% 0.11/0.39    inference(avatar_split_clause,[],[f145,f147,f118])).
% 0.11/0.39  fof(f145,plain,(
% 0.11/0.39    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) )),
% 0.11/0.39    inference(resolution,[],[f84,f58])).
% 0.11/0.39  fof(f58,plain,(
% 0.11/0.39    l1_pre_topc(sK0)),
% 0.11/0.39    inference(cnf_transformation,[],[f52])).
% 0.11/0.39  fof(f84,plain,(
% 0.11/0.39    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f42])).
% 0.11/0.39  fof(f42,plain,(
% 0.11/0.39    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.11/0.39    inference(flattening,[],[f41])).
% 0.11/0.39  fof(f41,plain,(
% 0.11/0.39    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.11/0.39    inference(ennf_transformation,[],[f21])).
% 0.11/0.39  fof(f21,axiom,(
% 0.11/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.11/0.39  fof(f133,plain,(
% 0.11/0.39    spl4_2),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f132])).
% 0.11/0.39  fof(f132,plain,(
% 0.11/0.39    $false | spl4_2),
% 0.11/0.39    inference(resolution,[],[f124,f58])).
% 0.11/0.39  fof(f124,plain,(
% 0.11/0.39    ~l1_pre_topc(sK0) | spl4_2),
% 0.11/0.39    inference(avatar_component_clause,[],[f122])).
% 0.11/0.39  fof(f131,plain,(
% 0.11/0.39    spl4_1),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f130])).
% 0.11/0.39  fof(f130,plain,(
% 0.11/0.39    $false | spl4_1),
% 0.11/0.39    inference(resolution,[],[f120,f57])).
% 0.11/0.39  fof(f57,plain,(
% 0.11/0.39    v2_pre_topc(sK0)),
% 0.11/0.39    inference(cnf_transformation,[],[f52])).
% 0.11/0.39  fof(f120,plain,(
% 0.11/0.39    ~v2_pre_topc(sK0) | spl4_1),
% 0.11/0.39    inference(avatar_component_clause,[],[f118])).
% 0.11/0.39  fof(f129,plain,(
% 0.11/0.39    ~spl4_1 | ~spl4_2 | spl4_3),
% 0.11/0.39    inference(avatar_split_clause,[],[f116,f126,f122,f118])).
% 0.11/0.39  fof(f116,plain,(
% 0.11/0.39    v4_pre_topc(u1_struct_0(sK0),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.11/0.39    inference(superposition,[],[f83,f112])).
% 0.11/0.39  fof(f112,plain,(
% 0.11/0.39    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.11/0.39    inference(resolution,[],[f111,f58])).
% 0.11/0.39  fof(f111,plain,(
% 0.11/0.39    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.11/0.39    inference(resolution,[],[f73,f74])).
% 0.11/0.39  fof(f74,plain,(
% 0.11/0.39    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f32])).
% 0.11/0.39  fof(f32,plain,(
% 0.11/0.39    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.11/0.39    inference(ennf_transformation,[],[f23])).
% 0.11/0.39  fof(f23,axiom,(
% 0.11/0.39    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.11/0.39  fof(f73,plain,(
% 0.11/0.39    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f31])).
% 0.11/0.39  fof(f31,plain,(
% 0.11/0.39    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.11/0.39    inference(ennf_transformation,[],[f22])).
% 0.11/0.39  fof(f22,axiom,(
% 0.11/0.39    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.11/0.39  fof(f83,plain,(
% 0.11/0.39    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f40])).
% 0.11/0.39  fof(f40,plain,(
% 0.11/0.39    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.11/0.39    inference(flattening,[],[f39])).
% 0.11/0.39  fof(f39,plain,(
% 0.11/0.39    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.11/0.39    inference(ennf_transformation,[],[f24])).
% 0.11/0.39  fof(f24,axiom,(
% 0.11/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.11/0.39  % SZS output end Proof for theBenchmark
% 0.11/0.39  % (21243)------------------------------
% 0.11/0.39  % (21243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.39  % (21243)Termination reason: Refutation
% 0.11/0.39  
% 0.11/0.39  % (21243)Memory used [KB]: 6268
% 0.11/0.39  % (21243)Time elapsed: 0.059 s
% 0.11/0.39  % (21243)------------------------------
% 0.11/0.39  % (21243)------------------------------
% 0.11/0.39  % (21240)Success in time 0.111 s
%------------------------------------------------------------------------------
