%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 175 expanded)
%              Number of leaves         :   20 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  311 (1015 expanded)
%              Number of equality atoms :   33 ( 136 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f116,f123,f140,f148,f151,f205,f210])).

fof(f210,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f208,f133,f129,f125,f99,f64,f60])).

fof(f60,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f64,plain,
    ( spl6_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f99,plain,
    ( spl6_7
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f125,plain,
    ( spl6_10
  <=> m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f129,plain,
    ( spl6_11
  <=> r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f133,plain,
    ( spl6_12
  <=> m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f208,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl6_12 ),
    inference(resolution,[],[f135,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
                    & v3_pre_topc(sK4(X0,X1,X4),X0)
                    & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
        & v3_pre_topc(sK4(X0,X1,X4),X0)
        & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
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
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f135,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f205,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_13 ),
    inference(avatar_split_clause,[],[f204,f137,f129,f125,f99,f64,f60])).

fof(f137,plain,
    ( spl6_13
  <=> v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f204,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl6_13 ),
    inference(resolution,[],[f139,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f139,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f151,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f150,f125])).

fof(f150,plain,(
    m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f141,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f141,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f79,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16,f15])).

fof(f15,plain,
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
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
                              & v3_pre_topc(X3,X0) ) )
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
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | r2_hidden(sK2,X0) ) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f29,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f148,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f146,f129])).

fof(f146,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(resolution,[],[f80,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f80,plain,(
    m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f29,f45])).

fof(f140,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f91,f137,f133,f129,f125,f99,f64,f60])).

fof(f91,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( sQ5_eqProxy(k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)),X4)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f34,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X3] :
      ( ~ sQ5_eqProxy(k9_subset_1(u1_struct_0(sK0),sK1,X3),k2_enumset1(sK2,sK2,sK2,sK2))
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(equality_proxy_replacement,[],[f44,f46])).

fof(f44,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_enumset1(sK2,sK2,sK2,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f30,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f123,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f66,f26])).

fof(f66,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f116,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f101,f27])).

fof(f27,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f101,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f93,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f62,f25])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (28006)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (27998)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (27995)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (27990)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (27987)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (27998)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (27983)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (28002)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (27985)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.53  % (27984)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.53  % SZS output start Proof for theBenchmark
% 1.37/0.53  fof(f211,plain,(
% 1.37/0.53    $false),
% 1.37/0.53    inference(avatar_sat_refutation,[],[f93,f116,f123,f140,f148,f151,f205,f210])).
% 1.37/0.53  fof(f210,plain,(
% 1.37/0.53    ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12),
% 1.37/0.53    inference(avatar_split_clause,[],[f208,f133,f129,f125,f99,f64,f60])).
% 1.37/0.53  fof(f60,plain,(
% 1.37/0.53    spl6_1 <=> l1_pre_topc(sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.37/0.53  fof(f64,plain,(
% 1.37/0.53    spl6_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.37/0.53  fof(f99,plain,(
% 1.37/0.53    spl6_7 <=> v2_tex_2(sK1,sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.37/0.53  fof(f125,plain,(
% 1.37/0.53    spl6_10 <=> m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.37/0.53  fof(f129,plain,(
% 1.37/0.53    spl6_11 <=> r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.37/0.53  fof(f133,plain,(
% 1.37/0.53    spl6_12 <=> m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.37/0.53  fof(f208,plain,(
% 1.37/0.53    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl6_12),
% 1.37/0.53    inference(resolution,[],[f135,f32])).
% 1.37/0.53  fof(f32,plain,(
% 1.37/0.53    ( ! [X4,X0,X1] : (m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f23])).
% 1.37/0.53  fof(f23,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4 & v3_pre_topc(sK4(X0,X1,X4),X0) & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f22,f21])).
% 1.37/0.53  fof(f21,plain,(
% 1.37/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f22,plain,(
% 1.37/0.53    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4 & v3_pre_topc(sK4(X0,X1,X4),X0) & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f20,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(rectify,[],[f19])).
% 1.37/0.53  fof(f19,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(nnf_transformation,[],[f12])).
% 1.37/0.53  fof(f12,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(flattening,[],[f11])).
% 1.37/0.53  fof(f11,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(ennf_transformation,[],[f6])).
% 1.37/0.53  fof(f6,axiom,(
% 1.37/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 1.37/0.53  fof(f135,plain,(
% 1.37/0.53    ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_12),
% 1.37/0.53    inference(avatar_component_clause,[],[f133])).
% 1.37/0.53  fof(f205,plain,(
% 1.37/0.53    ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_10 | ~spl6_11 | spl6_13),
% 1.37/0.53    inference(avatar_split_clause,[],[f204,f137,f129,f125,f99,f64,f60])).
% 1.37/0.53  fof(f137,plain,(
% 1.37/0.53    spl6_13 <=> v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.37/0.53  fof(f204,plain,(
% 1.37/0.53    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl6_13),
% 1.37/0.53    inference(resolution,[],[f139,f33])).
% 1.37/0.53  fof(f33,plain,(
% 1.37/0.53    ( ! [X4,X0,X1] : (v3_pre_topc(sK4(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f23])).
% 1.37/0.53  fof(f139,plain,(
% 1.37/0.53    ~v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) | spl6_13),
% 1.37/0.53    inference(avatar_component_clause,[],[f137])).
% 1.37/0.53  fof(f151,plain,(
% 1.37/0.53    spl6_10),
% 1.37/0.53    inference(avatar_split_clause,[],[f150,f125])).
% 1.37/0.53  fof(f150,plain,(
% 1.37/0.53    m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.53    inference(resolution,[],[f141,f45])).
% 1.37/0.53  fof(f45,plain,(
% 1.37/0.53    ( ! [X0,X1] : (m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.37/0.53    inference(definition_unfolding,[],[f39,f43])).
% 1.37/0.53  fof(f43,plain,(
% 1.37/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.37/0.53    inference(definition_unfolding,[],[f31,f38])).
% 1.37/0.53  fof(f38,plain,(
% 1.37/0.53    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f2])).
% 1.37/0.53  fof(f2,axiom,(
% 1.37/0.53    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.37/0.53  fof(f31,plain,(
% 1.37/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f1])).
% 1.37/0.53  fof(f1,axiom,(
% 1.37/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.37/0.53  fof(f39,plain,(
% 1.37/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f13])).
% 1.37/0.53  fof(f13,plain,(
% 1.37/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.37/0.53    inference(ennf_transformation,[],[f4])).
% 1.37/0.53  fof(f4,axiom,(
% 1.37/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.37/0.53  fof(f141,plain,(
% 1.37/0.53    r2_hidden(sK2,u1_struct_0(sK0))),
% 1.37/0.53    inference(resolution,[],[f79,f26])).
% 1.37/0.53  fof(f26,plain,(
% 1.37/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.53    inference(cnf_transformation,[],[f18])).
% 1.37/0.53  fof(f18,plain,(
% 1.37/0.53    ((! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.37/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16,f15])).
% 1.37/0.53  fof(f15,plain,(
% 1.37/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f16,plain,(
% 1.37/0.53    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f17,plain,(
% 1.37/0.53    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f10,plain,(
% 1.37/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.37/0.53    inference(flattening,[],[f9])).
% 1.37/0.53  fof(f9,plain,(
% 1.37/0.53    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.37/0.53    inference(ennf_transformation,[],[f8])).
% 1.37/0.53  fof(f8,negated_conjecture,(
% 1.37/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.37/0.53    inference(negated_conjecture,[],[f7])).
% 1.37/0.53  fof(f7,conjecture,(
% 1.37/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).
% 1.37/0.53  fof(f79,plain,(
% 1.37/0.53    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | r2_hidden(sK2,X0)) )),
% 1.37/0.53    inference(resolution,[],[f29,f40])).
% 1.37/0.53  fof(f40,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.53    inference(cnf_transformation,[],[f14])).
% 1.37/0.53  fof(f14,plain,(
% 1.37/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.53    inference(ennf_transformation,[],[f3])).
% 1.37/0.53  fof(f3,axiom,(
% 1.37/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.37/0.53  fof(f29,plain,(
% 1.37/0.53    r2_hidden(sK2,sK1)),
% 1.37/0.53    inference(cnf_transformation,[],[f18])).
% 1.37/0.53  fof(f148,plain,(
% 1.37/0.53    spl6_11),
% 1.37/0.53    inference(avatar_split_clause,[],[f146,f129])).
% 1.37/0.53  fof(f146,plain,(
% 1.37/0.53    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.37/0.53    inference(resolution,[],[f80,f41])).
% 1.37/0.53  fof(f41,plain,(
% 1.37/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.37/0.53    inference(cnf_transformation,[],[f24])).
% 1.37/0.53  fof(f24,plain,(
% 1.37/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.37/0.53    inference(nnf_transformation,[],[f5])).
% 1.37/0.53  fof(f5,axiom,(
% 1.37/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.37/0.53  fof(f80,plain,(
% 1.37/0.53    m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(sK1))),
% 1.37/0.53    inference(resolution,[],[f29,f45])).
% 1.37/0.53  fof(f140,plain,(
% 1.37/0.53    ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13),
% 1.37/0.53    inference(avatar_split_clause,[],[f91,f137,f133,f129,f125,f99,f64,f60])).
% 1.37/0.53  fof(f91,plain,(
% 1.37/0.53    ~v3_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.37/0.53    inference(resolution,[],[f47,f49])).
% 1.37/0.53  fof(f49,plain,(
% 1.37/0.53    ( ! [X4,X0,X1] : (sQ5_eqProxy(k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)),X4) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.53    inference(equality_proxy_replacement,[],[f34,f46])).
% 1.37/0.53  fof(f46,plain,(
% 1.37/0.53    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 1.37/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 1.37/0.53  fof(f34,plain,(
% 1.37/0.53    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f23])).
% 1.37/0.53  fof(f47,plain,(
% 1.37/0.53    ( ! [X3] : (~sQ5_eqProxy(k9_subset_1(u1_struct_0(sK0),sK1,X3),k2_enumset1(sK2,sK2,sK2,sK2)) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.37/0.53    inference(equality_proxy_replacement,[],[f44,f46])).
% 1.37/0.53  fof(f44,plain,(
% 1.37/0.53    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_enumset1(sK2,sK2,sK2,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.37/0.53    inference(definition_unfolding,[],[f30,f43])).
% 1.37/0.53  fof(f30,plain,(
% 1.37/0.53    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.37/0.53    inference(cnf_transformation,[],[f18])).
% 1.37/0.53  fof(f123,plain,(
% 1.37/0.53    spl6_2),
% 1.37/0.53    inference(avatar_contradiction_clause,[],[f121])).
% 1.37/0.53  fof(f121,plain,(
% 1.37/0.53    $false | spl6_2),
% 1.37/0.53    inference(resolution,[],[f66,f26])).
% 1.37/0.53  fof(f66,plain,(
% 1.37/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_2),
% 1.37/0.53    inference(avatar_component_clause,[],[f64])).
% 1.37/0.53  fof(f116,plain,(
% 1.37/0.53    spl6_7),
% 1.37/0.53    inference(avatar_contradiction_clause,[],[f113])).
% 1.37/0.53  fof(f113,plain,(
% 1.37/0.53    $false | spl6_7),
% 1.37/0.53    inference(resolution,[],[f101,f27])).
% 1.37/0.53  fof(f27,plain,(
% 1.37/0.53    v2_tex_2(sK1,sK0)),
% 1.37/0.53    inference(cnf_transformation,[],[f18])).
% 1.37/0.53  fof(f101,plain,(
% 1.37/0.53    ~v2_tex_2(sK1,sK0) | spl6_7),
% 1.37/0.53    inference(avatar_component_clause,[],[f99])).
% 1.37/0.53  fof(f93,plain,(
% 1.37/0.53    spl6_1),
% 1.37/0.53    inference(avatar_contradiction_clause,[],[f92])).
% 1.37/0.53  fof(f92,plain,(
% 1.37/0.53    $false | spl6_1),
% 1.37/0.53    inference(resolution,[],[f62,f25])).
% 1.37/0.53  fof(f25,plain,(
% 1.37/0.53    l1_pre_topc(sK0)),
% 1.37/0.53    inference(cnf_transformation,[],[f18])).
% 1.37/0.53  fof(f62,plain,(
% 1.37/0.53    ~l1_pre_topc(sK0) | spl6_1),
% 1.37/0.53    inference(avatar_component_clause,[],[f60])).
% 1.37/0.53  % SZS output end Proof for theBenchmark
% 1.37/0.53  % (27998)------------------------------
% 1.37/0.53  % (27998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (27998)Termination reason: Refutation
% 1.37/0.53  
% 1.37/0.53  % (27998)Memory used [KB]: 6268
% 1.37/0.53  % (27998)Time elapsed: 0.065 s
% 1.37/0.53  % (27998)------------------------------
% 1.37/0.53  % (27998)------------------------------
% 1.37/0.53  % (27982)Success in time 0.175 s
%------------------------------------------------------------------------------
