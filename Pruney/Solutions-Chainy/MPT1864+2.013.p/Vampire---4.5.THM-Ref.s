%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 269 expanded)
%              Number of leaves         :   24 ( 108 expanded)
%              Depth                    :   11
%              Number of atoms          :  368 (1612 expanded)
%              Number of equality atoms :   47 ( 216 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f102,f113,f118,f138,f154,f156,f164,f166,f173])).

fof(f173,plain,
    ( ~ spl7_10
    | ~ spl7_6
    | ~ spl7_13
    | spl7_7 ),
    inference(avatar_split_clause,[],[f171,f126,f161,f110,f140])).

fof(f140,plain,
    ( spl7_10
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f110,plain,
    ( spl7_6
  <=> m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f161,plain,
    ( spl7_13
  <=> r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f126,plain,
    ( spl7_7
  <=> m1_subset_1(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f171,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2)
    | spl7_7 ),
    inference(resolution,[],[f128,f41])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK5(X0,X1),X0)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
              & v3_pre_topc(sK6(X0,X1,X4),X1)
              & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK5(X0,X1),X0)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
        & v3_pre_topc(sK6(X0,X1,X4),X1)
        & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v3_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f128,plain,
    ( ~ m1_subset_1(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f166,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl7_13 ),
    inference(resolution,[],[f163,f71])).

fof(f71,plain,(
    r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) ),
    inference(resolution,[],[f70,f36])).

fof(f36,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
        | ~ v3_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                    | ~ v3_pre_topc(X3,X0)
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
                  | ~ v3_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                | ~ v3_pre_topc(X3,sK2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
              | ~ v3_pre_topc(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & r2_hidden(X2,sK3)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
            | ~ v3_pre_topc(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & r2_hidden(X2,sK3)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
          | ~ v3_pre_topc(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & r2_hidden(sK4,sK3)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r1_tarski(k2_enumset1(X0,X0,X0,sK4),sK3) ) ),
    inference(resolution,[],[f57,f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f163,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f164,plain,
    ( ~ spl7_10
    | ~ spl7_6
    | ~ spl7_13
    | spl7_9 ),
    inference(avatar_split_clause,[],[f159,f135,f161,f110,f140])).

fof(f135,plain,
    ( spl7_9
  <=> v3_pre_topc(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f159,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2)
    | spl7_9 ),
    inference(resolution,[],[f137,f42])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X4),X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f137,plain,
    ( ~ v3_pre_topc(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK2)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f156,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl7_12 ),
    inference(resolution,[],[f153,f34])).

fof(f34,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f153,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_12
  <=> v2_tex_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f154,plain,
    ( ~ spl7_3
    | ~ spl7_12
    | spl7_10 ),
    inference(avatar_split_clause,[],[f149,f140,f151,f93])).

fof(f93,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f149,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_10 ),
    inference(resolution,[],[f141,f62])).

fof(f62,plain,(
    ! [X1] :
      ( sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f60,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f13,f18,f17])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f141,plain,
    ( ~ sP0(sK3,sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f138,plain,
    ( ~ spl7_7
    | ~ spl7_9
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f124,f106,f135,f126])).

fof(f106,plain,
    ( spl7_5
  <=> k2_enumset1(sK4,sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f124,plain,
    ( ~ v3_pre_topc(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_5 ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | ~ v3_pre_topc(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_5 ),
    inference(superposition,[],[f56,f108])).

fof(f108,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f56,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k2_enumset1(sK4,sK4,sK4,sK4)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f115,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f115,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_6 ),
    inference(resolution,[],[f114,f71])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl7_6 ),
    inference(resolution,[],[f112,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f67,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f67,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f112,plain,
    ( ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f113,plain,
    ( spl7_5
    | ~ spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f104,f97,f110,f106])).

fof(f97,plain,
    ( spl7_4
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_tarski(X0,sK3)
        | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f104,plain,
    ( ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_enumset1(sK4,sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ spl7_4 ),
    inference(resolution,[],[f98,f71])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f102,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f95,f33])).

fof(f95,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f99,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f91,f97,f93])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0
      | ~ r1_tarski(X0,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f90,f34])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k9_subset_1(u1_struct_0(sK2),X1,sK6(X1,sK2,X0)) = X0
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f43,f62])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13655)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (13658)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (13654)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (13666)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (13666)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f99,f102,f113,f118,f138,f154,f156,f164,f166,f173])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ~spl7_10 | ~spl7_6 | ~spl7_13 | spl7_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f171,f126,f161,f110,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl7_10 <=> sP0(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl7_6 <=> m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    spl7_13 <=> r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl7_7 <=> m1_subset_1(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ~r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) | ~m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2) | spl7_7),
% 0.21/0.52    inference(resolution,[],[f128,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X4,X0,X1] : (m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v3_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f28,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v3_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl7_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    $false | spl7_13),
% 0.21/0.52    inference(resolution,[],[f163,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)),
% 0.21/0.52    inference(resolution,[],[f70,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    r2_hidden(sK4,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ((! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f22,f21,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) => (! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK3) | r1_tarski(k2_enumset1(X0,X0,X0,sK4),sK3)) )),
% 0.21/0.52    inference(resolution,[],[f57,f36])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f54,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) | spl7_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f161])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~spl7_10 | ~spl7_6 | ~spl7_13 | spl7_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f159,f135,f161,f110,f140])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl7_9 <=> v3_pre_topc(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) | ~m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2) | spl7_9),
% 0.21/0.52    inference(resolution,[],[f137,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X4,X0,X1] : (v3_pre_topc(sK6(X0,X1,X4),X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ~v3_pre_topc(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) | spl7_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f135])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl7_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    $false | spl7_12),
% 0.21/0.52    inference(resolution,[],[f153,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v2_tex_2(sK3,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ~v2_tex_2(sK3,sK2) | spl7_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl7_12 <=> v2_tex_2(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ~spl7_3 | ~spl7_12 | spl7_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f149,f140,f151,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~v2_tex_2(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_10),
% 0.21/0.52    inference(resolution,[],[f141,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X1] : (sP0(X1,sK2) | ~v2_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.52    inference(resolution,[],[f60,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.52    inference(resolution,[],[f47,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    l1_pre_topc(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(definition_folding,[],[f13,f18,f17])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~sP0(sK3,sK2) | spl7_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f140])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~spl7_7 | ~spl7_9 | ~spl7_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f124,f106,f135,f126])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl7_5 <=> k2_enumset1(sK4,sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ~v3_pre_topc(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4) | ~v3_pre_topc(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_5),
% 0.21/0.52    inference(superposition,[],[f56,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    k2_enumset1(sK4,sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4))) | ~spl7_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k2_enumset1(sK4,sK4,sK4,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f37,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f38,f48])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl7_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    $false | spl7_6),
% 0.21/0.52    inference(resolution,[],[f115,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_6),
% 0.21/0.52    inference(resolution,[],[f114,f71])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl7_6),
% 0.21/0.52    inference(resolution,[],[f112,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(superposition,[],[f67,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(superposition,[],[f50,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ~m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f110])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl7_5 | ~spl7_6 | ~spl7_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f104,f97,f110,f106])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl7_4 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK3) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | k2_enumset1(sK4,sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k2_enumset1(sK4,sK4,sK4,sK4))) | ~spl7_4),
% 0.21/0.52    inference(resolution,[],[f98,f71])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0) ) | ~spl7_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl7_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    $false | spl7_3),
% 0.21/0.52    inference(resolution,[],[f95,f33])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~spl7_3 | spl7_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f91,f97,f93])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 | ~r1_tarski(X0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.52    inference(resolution,[],[f90,f34])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_tex_2(X1,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),X1,sK6(X1,sK2,X0)) = X0 | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.52    inference(resolution,[],[f43,f62])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X4,X0,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (13666)------------------------------
% 0.21/0.52  % (13666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13666)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (13666)Memory used [KB]: 6268
% 0.21/0.52  % (13666)Time elapsed: 0.112 s
% 0.21/0.52  % (13666)------------------------------
% 0.21/0.52  % (13666)------------------------------
% 0.21/0.52  % (13673)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (13668)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13656)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (13682)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (13665)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (13671)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (13667)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (13674)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (13659)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (13671)Refutation not found, incomplete strategy% (13671)------------------------------
% 0.21/0.54  % (13671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13676)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (13662)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (13671)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13671)Memory used [KB]: 10746
% 0.21/0.54  % (13671)Time elapsed: 0.130 s
% 0.21/0.54  % (13671)------------------------------
% 0.21/0.54  % (13671)------------------------------
% 0.21/0.54  % (13672)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (13681)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (13676)Refutation not found, incomplete strategy% (13676)------------------------------
% 0.21/0.54  % (13676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13660)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (13653)Success in time 0.181 s
%------------------------------------------------------------------------------
