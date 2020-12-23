%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 220 expanded)
%              Number of leaves         :   23 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  360 (1244 expanded)
%              Number of equality atoms :   44 ( 167 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f92,f183,f200,f205,f206,f210,f218,f220,f226])).

fof(f226,plain,
    ( spl7_14
    | ~ spl7_19
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f225,f202,f87,f186,f157])).

fof(f157,plain,
    ( spl7_14
  <=> k2_tarski(sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_tarski(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f186,plain,
    ( spl7_19
  <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f87,plain,
    ( spl7_4
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_tarski(X0,sK3)
        | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f202,plain,
    ( spl7_20
  <=> r1_tarski(k2_tarski(sK4,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f225,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_tarski(sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_tarski(sK4,sK4)))
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(resolution,[],[f203,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f203,plain,
    ( r1_tarski(k2_tarski(sK4,sK4),sK3)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f220,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl7_21 ),
    inference(resolution,[],[f217,f32])).

fof(f32,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
        | ~ v4_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                  | ~ v4_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                | ~ v4_pre_topc(X3,sK2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
              | ~ v4_pre_topc(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & r2_hidden(X2,sK3)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
            | ~ v4_pre_topc(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & r2_hidden(X2,sK3)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
          | ~ v4_pre_topc(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & r2_hidden(sK4,sK3)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

fof(f217,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl7_21
  <=> v2_tex_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f218,plain,
    ( ~ spl7_3
    | ~ spl7_21
    | spl7_5 ),
    inference(avatar_split_clause,[],[f212,f99,f215,f83])).

fof(f83,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f99,plain,
    ( spl7_5
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f212,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_5 ),
    inference(resolution,[],[f100,f56])).

fof(f56,plain,(
    ! [X1] :
      ( sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f54,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f45,f30])).

fof(f30,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f17,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(f100,plain,
    ( ~ sP0(sK3,sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f210,plain,(
    spl7_20 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl7_20 ),
    inference(resolution,[],[f207,f34])).

fof(f34,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f207,plain,
    ( ~ r2_hidden(sK4,sK3)
    | spl7_20 ),
    inference(resolution,[],[f204,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f204,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK4),sK3)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f206,plain,
    ( ~ spl7_5
    | ~ spl7_19
    | ~ spl7_20
    | spl7_18 ),
    inference(avatar_split_clause,[],[f191,f180,f202,f186,f99])).

fof(f180,plain,
    ( spl7_18
  <=> v4_pre_topc(sK6(sK3,sK2,k2_tarski(sK4,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f191,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK4),sK3)
    | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2)
    | spl7_18 ),
    inference(resolution,[],[f182,f40])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK6(X0,X1,X4),X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1)
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK5(X0,X1),X0)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
              & v4_pre_topc(sK6(X0,X1,X4),X1)
              & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK5(X0,X1),X0)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v4_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
        & v4_pre_topc(sK6(X0,X1,X4),X1)
        & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v4_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v4_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

% (26446)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f24,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f182,plain,
    ( ~ v4_pre_topc(sK6(sK3,sK2,k2_tarski(sK4,sK4)),sK2)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f205,plain,
    ( ~ spl7_5
    | ~ spl7_19
    | ~ spl7_20
    | spl7_16 ),
    inference(avatar_split_clause,[],[f192,f171,f202,f186,f99])).

fof(f171,plain,
    ( spl7_16
  <=> m1_subset_1(sK6(sK3,sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f192,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK4),sK3)
    | ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2)
    | spl7_16 ),
    inference(resolution,[],[f173,f39])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f173,plain,
    ( ~ m1_subset_1(sK6(sK3,sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f171])).

fof(f200,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl7_19 ),
    inference(resolution,[],[f195,f31])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f195,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_19 ),
    inference(resolution,[],[f194,f34])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl7_19 ),
    inference(resolution,[],[f190,f52])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_tarski(sK4,sK4),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl7_19 ),
    inference(resolution,[],[f187,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f61,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f61,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f49,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f187,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f183,plain,
    ( ~ spl7_16
    | ~ spl7_18
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f169,f157,f180,f171])).

fof(f169,plain,
    ( ~ v4_pre_topc(sK6(sK3,sK2,k2_tarski(sK4,sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_14 ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,
    ( k2_tarski(sK4,sK4) != k2_tarski(sK4,sK4)
    | ~ v4_pre_topc(sK6(sK3,sK2,k2_tarski(sK4,sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_14 ),
    inference(superposition,[],[f51,f159])).

fof(f159,plain,
    ( k2_tarski(sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_tarski(sK4,sK4)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f51,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k2_tarski(sK4,sK4)
      | ~ v4_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
      | ~ v4_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f92,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f85,f31])).

fof(f85,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f89,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f81,f87,f83])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0
      | ~ r1_tarski(X0,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f80,f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k9_subset_1(u1_struct_0(sK2),X1,sK6(X1,sK2,X0)) = X0
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f41,f56])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26451)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (26438)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (26439)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (26449)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (26440)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (26447)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (26448)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (26458)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (26454)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (26459)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (26458)Refutation not found, incomplete strategy% (26458)------------------------------
% 0.20/0.53  % (26458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26450)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (26458)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26458)Memory used [KB]: 1663
% 0.20/0.53  % (26458)Time elapsed: 0.116 s
% 0.20/0.53  % (26458)------------------------------
% 0.20/0.53  % (26458)------------------------------
% 0.20/0.53  % (26457)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (26449)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f89,f92,f183,f200,f205,f206,f210,f218,f220,f226])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    spl7_14 | ~spl7_19 | ~spl7_4 | ~spl7_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f225,f202,f87,f186,f157])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    spl7_14 <=> k2_tarski(sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_tarski(sK4,sK4)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    spl7_19 <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl7_4 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK3) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    spl7_20 <=> r1_tarski(k2_tarski(sK4,sK4),sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | k2_tarski(sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_tarski(sK4,sK4))) | (~spl7_4 | ~spl7_20)),
% 0.20/0.53    inference(resolution,[],[f203,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0) ) | ~spl7_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f87])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    r1_tarski(k2_tarski(sK4,sK4),sK3) | ~spl7_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f202])).
% 0.20/0.53  fof(f220,plain,(
% 0.20/0.53    spl7_21),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f219])).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    $false | spl7_21),
% 0.20/0.53    inference(resolution,[],[f217,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    v2_tex_2(sK3,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ((! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f21,f20,f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) => (! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f7])).
% 0.20/0.53  fof(f7,conjecture,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).
% 0.20/0.53  fof(f217,plain,(
% 0.20/0.53    ~v2_tex_2(sK3,sK2) | spl7_21),
% 0.20/0.53    inference(avatar_component_clause,[],[f215])).
% 0.20/0.53  fof(f215,plain,(
% 0.20/0.53    spl7_21 <=> v2_tex_2(sK3,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    ~spl7_3 | ~spl7_21 | spl7_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f212,f99,f215,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl7_5 <=> sP0(sK3,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    ~v2_tex_2(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_5),
% 0.20/0.53    inference(resolution,[],[f100,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X1] : (sP0(X1,sK2) | ~v2_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.53    inference(resolution,[],[f54,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.53    inference(resolution,[],[f45,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    l1_pre_topc(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(definition_folding,[],[f12,f17,f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ~sP0(sK3,sK2) | spl7_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f99])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    spl7_20),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f208])).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    $false | spl7_20),
% 0.20/0.53    inference(resolution,[],[f207,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    r2_hidden(sK4,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ~r2_hidden(sK4,sK3) | spl7_20),
% 0.20/0.53    inference(resolution,[],[f204,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f48,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    ~r1_tarski(k2_tarski(sK4,sK4),sK3) | spl7_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f202])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    ~spl7_5 | ~spl7_19 | ~spl7_20 | spl7_18),
% 0.20/0.53    inference(avatar_split_clause,[],[f191,f180,f202,f186,f99])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    spl7_18 <=> v4_pre_topc(sK6(sK3,sK2,k2_tarski(sK4,sK4)),sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ~r1_tarski(k2_tarski(sK4,sK4),sK3) | ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2) | spl7_18),
% 0.20/0.53    inference(resolution,[],[f182,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (v4_pre_topc(sK6(X0,X1,X4),X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v4_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f27,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v4_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f24])).
% 0.20/0.53  % (26446)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    ~v4_pre_topc(sK6(sK3,sK2,k2_tarski(sK4,sK4)),sK2) | spl7_18),
% 0.20/0.53    inference(avatar_component_clause,[],[f180])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    ~spl7_5 | ~spl7_19 | ~spl7_20 | spl7_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f192,f171,f202,f186,f99])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    spl7_16 <=> m1_subset_1(sK6(sK3,sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    ~r1_tarski(k2_tarski(sK4,sK4),sK3) | ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2) | spl7_16),
% 0.20/0.53    inference(resolution,[],[f173,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    ~m1_subset_1(sK6(sK3,sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f171])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    spl7_19),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f198])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    $false | spl7_19),
% 0.20/0.53    inference(resolution,[],[f195,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_19),
% 0.20/0.53    inference(resolution,[],[f194,f34])).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl7_19),
% 0.20/0.53    inference(resolution,[],[f190,f52])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k2_tarski(sK4,sK4),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl7_19),
% 0.20/0.53    inference(resolution,[],[f187,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(superposition,[],[f61,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X2,X3,X1] : (m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X1))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X3,X1] : (m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X1))) )),
% 0.20/0.53    inference(superposition,[],[f49,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f186])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    ~spl7_16 | ~spl7_18 | ~spl7_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f169,f157,f180,f171])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ~v4_pre_topc(sK6(sK3,sK2,k2_tarski(sK4,sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_14),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f165])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    k2_tarski(sK4,sK4) != k2_tarski(sK4,sK4) | ~v4_pre_topc(sK6(sK3,sK2,k2_tarski(sK4,sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k2_tarski(sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_14),
% 0.20/0.53    inference(superposition,[],[f51,f159])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    k2_tarski(sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_tarski(sK4,sK4))) | ~spl7_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f157])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k2_tarski(sK4,sK4) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f35,f36])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    spl7_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    $false | spl7_3),
% 0.20/0.53    inference(resolution,[],[f85,f31])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f83])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ~spl7_3 | spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f81,f87,f83])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 | ~r1_tarski(X0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.53    inference(resolution,[],[f80,f32])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_tex_2(X1,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),X1,sK6(X1,sK2,X0)) = X0 | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.53    inference(resolution,[],[f41,f56])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (26449)------------------------------
% 0.20/0.53  % (26449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26449)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (26449)Memory used [KB]: 6268
% 0.20/0.53  % (26449)Time elapsed: 0.118 s
% 0.20/0.53  % (26449)------------------------------
% 0.20/0.53  % (26449)------------------------------
% 0.20/0.53  % (26436)Success in time 0.173 s
%------------------------------------------------------------------------------
