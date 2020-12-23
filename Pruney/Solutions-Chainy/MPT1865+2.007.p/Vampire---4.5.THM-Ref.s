%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:01 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 235 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   10
%              Number of atoms          :  417 (1388 expanded)
%              Number of equality atoms :   44 ( 180 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f762,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f155,f169,f184,f199,f216,f242,f390,f742,f759,f760])).

fof(f760,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_15
    | ~ spl8_16
    | spl8_17 ),
    inference(avatar_split_clause,[],[f261,f209,f205,f201,f161,f101,f97])).

fof(f97,plain,
    ( spl8_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f101,plain,
    ( spl8_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f161,plain,
    ( spl8_12
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f201,plain,
    ( spl8_15
  <=> m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f205,plain,
    ( spl8_16
  <=> r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f209,plain,
    ( spl8_17
  <=> m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f261,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl8_17 ),
    inference(resolution,[],[f211,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
                    & v4_pre_topc(sK4(X0,X1,X4),X0)
                    & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
        & v4_pre_topc(sK4(X0,X1,X4),X0)
        & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
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
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f211,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f209])).

fof(f759,plain,
    ( ~ spl8_16
    | ~ spl8_15
    | ~ spl8_4
    | spl8_18 ),
    inference(avatar_split_clause,[],[f281,f213,f109,f201,f205])).

fof(f109,plain,
    ( spl8_4
  <=> ! [X1] :
        ( v4_pre_topc(sK4(sK0,sK1,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f213,plain,
    ( spl8_18
  <=> v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f281,plain,
    ( ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ spl8_4
    | spl8_18 ),
    inference(resolution,[],[f110,f215])).

fof(f215,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f213])).

fof(f110,plain,
    ( ! [X1] :
        ( v4_pre_topc(sK4(sK0,sK1,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK1) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f742,plain,
    ( ~ spl8_7
    | spl8_15 ),
    inference(avatar_split_clause,[],[f739,f201,f127])).

fof(f127,plain,
    ( spl8_7
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f739,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl8_15 ),
    inference(duplicate_literal_removal,[],[f738])).

fof(f738,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl8_15 ),
    inference(resolution,[],[f456,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f456,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),u1_struct_0(sK0))
    | spl8_15 ),
    inference(resolution,[],[f227,f78])).

fof(f78,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK6(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r1_tarski(sK6(X0,X1),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK6(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( r1_tarski(sK6(X0,X1),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f227,plain,
    ( ~ r2_hidden(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_15 ),
    inference(resolution,[],[f203,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f203,plain,
    ( ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f201])).

fof(f390,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f221,f123])).

fof(f123,plain,
    ( spl8_6
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f221,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f116,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
        | ~ v4_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).

fof(f24,plain,
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
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
          | ~ v4_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f47,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f47,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f242,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f233,f205])).

fof(f233,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(resolution,[],[f117,f47])).

fof(f117,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r1_tarski(k2_enumset1(sK2,sK2,sK2,X1),sK1) ) ),
    inference(resolution,[],[f47,f75])).

fof(f216,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f175,f213,f209,f205,f201,f161,f101,f97])).

fof(f175,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f81,f83])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( sQ7_eqProxy(k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)),X4)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f52,f80])).

fof(f80,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    ! [X3] :
      ( ~ sQ7_eqProxy(k9_subset_1(u1_struct_0(sK0),sK1,X3),k2_enumset1(sK2,sK2,sK2,sK2))
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(equality_proxy_replacement,[],[f73,f80])).

fof(f73,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_enumset1(sK2,sK2,sK2,sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f199,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl8_2 ),
    inference(resolution,[],[f103,f44])).

fof(f103,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f184,plain,(
    spl8_12 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl8_12 ),
    inference(resolution,[],[f163,f45])).

fof(f45,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f163,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f169,plain,
    ( ~ spl8_1
    | ~ spl8_12
    | spl8_4 ),
    inference(avatar_split_clause,[],[f133,f109,f161,f97])).

fof(f133,plain,(
    ! [X2] :
      ( v4_pre_topc(sK4(sK0,sK1,X2),sK0)
      | ~ r1_tarski(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f155,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f99,f43])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f130,plain,
    ( spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f121,f127,f123])).

fof(f121,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.54  % (25516)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (25508)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (25500)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.56  % (25507)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.57  % (25497)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.50/0.57  % (25494)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.57  % (25495)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.57  % (25498)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.50/0.57  % (25493)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.50/0.57  % (25496)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.50/0.57  % (25499)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.58  % (25508)Refutation found. Thanks to Tanya!
% 1.50/0.58  % SZS status Theorem for theBenchmark
% 1.50/0.58  % SZS output start Proof for theBenchmark
% 1.50/0.58  fof(f762,plain,(
% 1.50/0.58    $false),
% 1.50/0.58    inference(avatar_sat_refutation,[],[f130,f155,f169,f184,f199,f216,f242,f390,f742,f759,f760])).
% 1.50/0.58  fof(f760,plain,(
% 1.50/0.58    ~spl8_1 | ~spl8_2 | ~spl8_12 | ~spl8_15 | ~spl8_16 | spl8_17),
% 1.50/0.58    inference(avatar_split_clause,[],[f261,f209,f205,f201,f161,f101,f97])).
% 1.50/0.58  fof(f97,plain,(
% 1.50/0.58    spl8_1 <=> l1_pre_topc(sK0)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.50/0.58  fof(f101,plain,(
% 1.50/0.58    spl8_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.50/0.58  fof(f161,plain,(
% 1.50/0.58    spl8_12 <=> v2_tex_2(sK1,sK0)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.50/0.58  fof(f201,plain,(
% 1.50/0.58    spl8_15 <=> m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.50/0.58  fof(f205,plain,(
% 1.50/0.58    spl8_16 <=> r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.50/0.58  fof(f209,plain,(
% 1.50/0.58    spl8_17 <=> m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.50/0.58  fof(f261,plain,(
% 1.50/0.58    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl8_17),
% 1.50/0.58    inference(resolution,[],[f211,f50])).
% 1.50/0.58  fof(f50,plain,(
% 1.50/0.58    ( ! [X4,X0,X1] : (m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f32])).
% 1.50/0.58  fof(f32,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4 & v4_pre_topc(sK4(X0,X1,X4),X0) & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f31,f30])).
% 1.50/0.58  fof(f30,plain,(
% 1.50/0.58    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.50/0.58    introduced(choice_axiom,[])).
% 1.50/0.58  fof(f31,plain,(
% 1.50/0.58    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4 & v4_pre_topc(sK4(X0,X1,X4),X0) & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.50/0.58    introduced(choice_axiom,[])).
% 1.50/0.58  fof(f29,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.58    inference(rectify,[],[f28])).
% 1.50/0.58  fof(f28,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.58    inference(nnf_transformation,[],[f17])).
% 1.50/0.58  fof(f17,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.58    inference(flattening,[],[f16])).
% 1.50/0.58  fof(f16,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.50/0.58    inference(ennf_transformation,[],[f11])).
% 1.50/0.58  fof(f11,axiom,(
% 1.50/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 1.50/0.58  fof(f211,plain,(
% 1.50/0.58    ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_17),
% 1.50/0.58    inference(avatar_component_clause,[],[f209])).
% 1.50/0.58  fof(f759,plain,(
% 1.50/0.58    ~spl8_16 | ~spl8_15 | ~spl8_4 | spl8_18),
% 1.50/0.58    inference(avatar_split_clause,[],[f281,f213,f109,f201,f205])).
% 1.50/0.58  fof(f109,plain,(
% 1.50/0.58    spl8_4 <=> ! [X1] : (v4_pre_topc(sK4(sK0,sK1,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.50/0.58  fof(f213,plain,(
% 1.50/0.58    spl8_18 <=> v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.50/0.58  fof(f281,plain,(
% 1.50/0.58    ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | (~spl8_4 | spl8_18)),
% 1.50/0.58    inference(resolution,[],[f110,f215])).
% 1.50/0.58  fof(f215,plain,(
% 1.50/0.58    ~v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) | spl8_18),
% 1.50/0.58    inference(avatar_component_clause,[],[f213])).
% 1.50/0.58  fof(f110,plain,(
% 1.50/0.58    ( ! [X1] : (v4_pre_topc(sK4(sK0,sK1,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1)) ) | ~spl8_4),
% 1.50/0.58    inference(avatar_component_clause,[],[f109])).
% 1.50/0.58  fof(f742,plain,(
% 1.50/0.58    ~spl8_7 | spl8_15),
% 1.50/0.58    inference(avatar_split_clause,[],[f739,f201,f127])).
% 1.50/0.58  fof(f127,plain,(
% 1.50/0.58    spl8_7 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.50/0.58  fof(f739,plain,(
% 1.50/0.58    ~r2_hidden(sK2,u1_struct_0(sK0)) | spl8_15),
% 1.50/0.58    inference(duplicate_literal_removal,[],[f738])).
% 1.50/0.58  fof(f738,plain,(
% 1.50/0.58    ~r2_hidden(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK2,u1_struct_0(sK0)) | spl8_15),
% 1.50/0.58    inference(resolution,[],[f456,f75])).
% 1.50/0.58  fof(f75,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f69,f71])).
% 1.50/0.58  fof(f71,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.50/0.58    inference(definition_unfolding,[],[f58,f66])).
% 1.50/0.58  fof(f66,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f4])).
% 1.50/0.58  fof(f4,axiom,(
% 1.50/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.58  fof(f58,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f3])).
% 1.50/0.58  fof(f3,axiom,(
% 1.50/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.67/0.58  fof(f69,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f42])).
% 1.67/0.58  fof(f42,plain,(
% 1.67/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.67/0.58    inference(flattening,[],[f41])).
% 1.67/0.58  fof(f41,plain,(
% 1.67/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.67/0.58    inference(nnf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.67/0.58  fof(f456,plain,(
% 1.67/0.58    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),u1_struct_0(sK0)) | spl8_15),
% 1.67/0.58    inference(resolution,[],[f227,f78])).
% 1.67/0.58  fof(f78,plain,(
% 1.67/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.67/0.58    inference(equality_resolution,[],[f63])).
% 1.67/0.58  fof(f63,plain,(
% 1.67/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f40,plain,(
% 1.67/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 1.67/0.58  fof(f39,plain,(
% 1.67/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK6(X0,X1),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f38,plain,(
% 1.67/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.67/0.58    inference(rectify,[],[f37])).
% 1.67/0.58  fof(f37,plain,(
% 1.67/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.67/0.58    inference(nnf_transformation,[],[f5])).
% 1.67/0.58  fof(f5,axiom,(
% 1.67/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.67/0.58  fof(f227,plain,(
% 1.67/0.58    ~r2_hidden(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_15),
% 1.67/0.58    inference(resolution,[],[f203,f59])).
% 1.67/0.58  fof(f59,plain,(
% 1.67/0.58    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f18])).
% 1.67/0.58  fof(f18,plain,(
% 1.67/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.67/0.58    inference(ennf_transformation,[],[f7])).
% 1.67/0.58  fof(f7,axiom,(
% 1.67/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.67/0.58  fof(f203,plain,(
% 1.67/0.58    ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_15),
% 1.67/0.58    inference(avatar_component_clause,[],[f201])).
% 1.67/0.58  fof(f390,plain,(
% 1.67/0.58    ~spl8_6),
% 1.67/0.58    inference(avatar_split_clause,[],[f221,f123])).
% 1.67/0.58  fof(f123,plain,(
% 1.67/0.58    spl8_6 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.67/0.58  fof(f221,plain,(
% 1.67/0.58    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.67/0.58    inference(resolution,[],[f116,f44])).
% 1.67/0.58  fof(f44,plain,(
% 1.67/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/0.58    inference(cnf_transformation,[],[f27])).
% 1.67/0.58  fof(f27,plain,(
% 1.67/0.58    ((! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).
% 1.67/0.58  fof(f24,plain,(
% 1.67/0.58    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f25,plain,(
% 1.67/0.58    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f26,plain,(
% 1.67/0.58    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f15,plain,(
% 1.67/0.58    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.67/0.58    inference(flattening,[],[f14])).
% 1.67/0.58  fof(f14,plain,(
% 1.67/0.58    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f13])).
% 1.67/0.58  fof(f13,negated_conjecture,(
% 1.67/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.67/0.58    inference(negated_conjecture,[],[f12])).
% 1.67/0.58  fof(f12,conjecture,(
% 1.67/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).
% 1.67/0.58  fof(f116,plain,(
% 1.67/0.58    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.67/0.58    inference(resolution,[],[f47,f70])).
% 1.67/0.58  fof(f70,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f23])).
% 1.67/0.58  fof(f23,plain,(
% 1.67/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.67/0.58    inference(ennf_transformation,[],[f9])).
% 1.67/0.58  fof(f9,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.67/0.59  fof(f47,plain,(
% 1.67/0.59    r2_hidden(sK2,sK1)),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f242,plain,(
% 1.67/0.59    spl8_16),
% 1.67/0.59    inference(avatar_split_clause,[],[f233,f205])).
% 1.67/0.59  fof(f233,plain,(
% 1.67/0.59    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.67/0.59    inference(resolution,[],[f117,f47])).
% 1.67/0.59  fof(f117,plain,(
% 1.67/0.59    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(k2_enumset1(sK2,sK2,sK2,X1),sK1)) )),
% 1.67/0.59    inference(resolution,[],[f47,f75])).
% 1.67/0.59  fof(f216,plain,(
% 1.67/0.59    ~spl8_1 | ~spl8_2 | ~spl8_12 | ~spl8_15 | ~spl8_16 | ~spl8_17 | ~spl8_18),
% 1.67/0.59    inference(avatar_split_clause,[],[f175,f213,f209,f205,f201,f161,f101,f97])).
% 1.67/0.59  fof(f175,plain,(
% 1.67/0.59    ~v4_pre_topc(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k2_enumset1(sK2,sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~m1_subset_1(k2_enumset1(sK2,sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.67/0.59    inference(resolution,[],[f81,f83])).
% 1.67/0.59  fof(f83,plain,(
% 1.67/0.59    ( ! [X4,X0,X1] : (sQ7_eqProxy(k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)),X4) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/0.59    inference(equality_proxy_replacement,[],[f52,f80])).
% 1.67/0.59  fof(f80,plain,(
% 1.67/0.59    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 1.67/0.59    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 1.67/0.59  fof(f52,plain,(
% 1.67/0.59    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f32])).
% 1.67/0.59  fof(f81,plain,(
% 1.67/0.59    ( ! [X3] : (~sQ7_eqProxy(k9_subset_1(u1_struct_0(sK0),sK1,X3),k2_enumset1(sK2,sK2,sK2,sK2)) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.67/0.59    inference(equality_proxy_replacement,[],[f73,f80])).
% 1.67/0.59  fof(f73,plain,(
% 1.67/0.59    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_enumset1(sK2,sK2,sK2,sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.67/0.59    inference(definition_unfolding,[],[f48,f72])).
% 1.67/0.59  fof(f72,plain,(
% 1.67/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.67/0.59    inference(definition_unfolding,[],[f49,f71])).
% 1.67/0.59  fof(f49,plain,(
% 1.67/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f2])).
% 1.67/0.59  fof(f2,axiom,(
% 1.67/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.67/0.59  fof(f48,plain,(
% 1.67/0.59    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f199,plain,(
% 1.67/0.59    spl8_2),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f197])).
% 1.67/0.59  fof(f197,plain,(
% 1.67/0.59    $false | spl8_2),
% 1.67/0.59    inference(resolution,[],[f103,f44])).
% 1.67/0.59  fof(f103,plain,(
% 1.67/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl8_2),
% 1.67/0.59    inference(avatar_component_clause,[],[f101])).
% 1.67/0.59  fof(f184,plain,(
% 1.67/0.59    spl8_12),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f181])).
% 1.67/0.59  fof(f181,plain,(
% 1.67/0.59    $false | spl8_12),
% 1.67/0.59    inference(resolution,[],[f163,f45])).
% 1.67/0.59  fof(f45,plain,(
% 1.67/0.59    v2_tex_2(sK1,sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f163,plain,(
% 1.67/0.59    ~v2_tex_2(sK1,sK0) | spl8_12),
% 1.67/0.59    inference(avatar_component_clause,[],[f161])).
% 1.67/0.59  fof(f169,plain,(
% 1.67/0.59    ~spl8_1 | ~spl8_12 | spl8_4),
% 1.67/0.59    inference(avatar_split_clause,[],[f133,f109,f161,f97])).
% 1.67/0.59  fof(f133,plain,(
% 1.67/0.59    ( ! [X2] : (v4_pre_topc(sK4(sK0,sK1,X2),sK0) | ~r1_tarski(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)) )),
% 1.67/0.59    inference(resolution,[],[f44,f51])).
% 1.67/0.59  fof(f51,plain,(
% 1.67/0.59    ( ! [X4,X0,X1] : (v4_pre_topc(sK4(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f32])).
% 1.67/0.59  fof(f155,plain,(
% 1.67/0.59    spl8_1),
% 1.67/0.59    inference(avatar_contradiction_clause,[],[f154])).
% 1.67/0.59  fof(f154,plain,(
% 1.67/0.59    $false | spl8_1),
% 1.67/0.59    inference(resolution,[],[f99,f43])).
% 1.67/0.59  fof(f43,plain,(
% 1.67/0.59    l1_pre_topc(sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f99,plain,(
% 1.67/0.59    ~l1_pre_topc(sK0) | spl8_1),
% 1.67/0.59    inference(avatar_component_clause,[],[f97])).
% 1.67/0.59  fof(f130,plain,(
% 1.67/0.59    spl8_6 | spl8_7),
% 1.67/0.59    inference(avatar_split_clause,[],[f121,f127,f123])).
% 1.67/0.59  fof(f121,plain,(
% 1.67/0.59    r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.67/0.59    inference(resolution,[],[f46,f60])).
% 1.67/0.59  fof(f60,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f20])).
% 1.67/0.59  fof(f20,plain,(
% 1.67/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.67/0.59    inference(flattening,[],[f19])).
% 1.67/0.59  fof(f19,plain,(
% 1.67/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f8])).
% 1.67/0.59  fof(f8,axiom,(
% 1.67/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.67/0.59  fof(f46,plain,(
% 1.67/0.59    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  % SZS output end Proof for theBenchmark
% 1.67/0.59  % (25508)------------------------------
% 1.67/0.59  % (25508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (25508)Termination reason: Refutation
% 1.67/0.59  
% 1.67/0.59  % (25508)Memory used [KB]: 6652
% 1.67/0.59  % (25508)Time elapsed: 0.097 s
% 1.67/0.59  % (25508)------------------------------
% 1.67/0.59  % (25508)------------------------------
% 1.67/0.59  % (25492)Success in time 0.225 s
%------------------------------------------------------------------------------
