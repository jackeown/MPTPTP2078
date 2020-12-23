%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1366+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 390 expanded)
%              Number of leaves         :   32 ( 200 expanded)
%              Depth                    :   10
%              Number of atoms          :  830 (3036 expanded)
%              Number of equality atoms :   26 ( 122 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f676,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f167,f210,f212,f213,f214,f215,f225,f227,f229,f231,f244,f313,f367,f372,f377,f382,f387,f392,f448,f675])).

fof(f675,plain,
    ( ~ spl8_8
    | ~ spl8_3
    | ~ spl8_46
    | ~ spl8_48
    | ~ spl8_50
    | ~ spl8_34
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f669,f446,f311,f389,f379,f369,f85,f109])).

fof(f109,plain,
    ( spl8_8
  <=> r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f85,plain,
    ( spl8_3
  <=> m1_subset_1(sK1(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

% (5964)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f369,plain,
    ( spl8_46
  <=> r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f379,plain,
    ( spl8_48
  <=> v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f389,plain,
    ( spl8_50
  <=> m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f311,plain,
    ( spl8_34
  <=> ! [X2] :
        ( r1_xboole_0(sK5(sK0,sK2(sK0),X2),sK6(sK0,sK2(sK0),X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK2(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f446,plain,
    ( spl8_58
  <=> ! [X1] :
        ( ~ r1_xboole_0(X1,sK6(sK0,sK2(sK0),sK1(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | ~ r2_hidden(sK1(sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f669,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ spl8_34
    | ~ spl8_58 ),
    inference(resolution,[],[f447,f312])).

fof(f312,plain,
    ( ! [X2] :
        ( r1_xboole_0(sK5(sK0,sK2(sK0),X2),sK6(sK0,sK2(sK0),X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK2(sK0))) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f311])).

fof(f447,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK6(sK0,sK2(sK0),sK1(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | ~ r2_hidden(sK1(sK0),X1) )
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f446])).

fof(f448,plain,
    ( spl8_20
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_49
    | ~ spl8_45
    | spl8_58
    | spl8_4
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f436,f374,f89,f446,f364,f384,f81,f77,f201])).

fof(f201,plain,
    ( spl8_20
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f77,plain,
    ( spl8_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f81,plain,
    ( spl8_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f384,plain,
    ( spl8_49
  <=> m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f364,plain,
    ( spl8_45
  <=> r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f89,plain,
    ( spl8_4
  <=> v9_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f374,plain,
    ( spl8_47
  <=> v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f436,plain,
    ( ! [X1] :
        ( v9_pre_topc(sK0)
        | ~ r1_xboole_0(X1,sK6(sK0,sK2(sK0),sK1(sK0)))
        | ~ r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
        | ~ r2_hidden(sK1(sK0),X1)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_47 ),
    inference(resolution,[],[f376,f45])).

fof(f45,plain,(
    ! [X4,X0,X3] :
      ( v9_pre_topc(X0)
      | ~ r1_xboole_0(X3,X4)
      | ~ r1_tarski(sK2(X0),X4)
      | ~ r2_hidden(sK1(X0),X3)
      | ~ v3_pre_topc(X4,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
          | ( ! [X3] :
                ( ! [X4] :
                    ( ~ r1_xboole_0(X3,X4)
                    | ~ r1_tarski(sK2(X0),X4)
                    | ~ r2_hidden(sK1(X0),X3)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
            & v4_pre_topc(sK2(X0),X0)
            & k1_xboole_0 != sK2(X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( r1_xboole_0(sK3(X0,X5,X6),sK4(X0,X5,X6))
                    & r1_tarski(X6,sK4(X0,X5,X6))
                    & r2_hidden(X5,sK3(X0,X5,X6))
                    & v3_pre_topc(sK4(X0,X5,X6),X0)
                    & v3_pre_topc(sK3(X0,X5,X6),X0)
                    & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0)))
                    & m1_subset_1(sK3(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6))
                  | ~ v4_pre_topc(X6,X0)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f21,f20,f19,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ~ r1_xboole_0(X3,X4)
                      | ~ r1_tarski(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
              & v4_pre_topc(X2,X0)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ! [X4] :
                    ( ~ r1_xboole_0(X3,X4)
                    | ~ r1_tarski(X2,X4)
                    | ~ r2_hidden(sK1(X0),X3)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),X2))
            & v4_pre_topc(X2,X0)
            & k1_xboole_0 != X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ~ r1_xboole_0(X3,X4)
                  | ~ r1_tarski(X2,X4)
                  | ~ r2_hidden(sK1(X0),X3)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),X2))
          & v4_pre_topc(X2,X0)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( ! [X4] :
                ( ~ r1_xboole_0(X3,X4)
                | ~ r1_tarski(sK2(X0),X4)
                | ~ r2_hidden(sK1(X0),X3)
                | ~ v3_pre_topc(X4,X0)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
        & v4_pre_topc(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( r1_xboole_0(X7,X8)
              & r1_tarski(X6,X8)
              & r2_hidden(X5,X7)
              & v3_pre_topc(X8,X0)
              & v3_pre_topc(X7,X0)
              & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X8] :
            ( r1_xboole_0(sK3(X0,X5,X6),X8)
            & r1_tarski(X6,X8)
            & r2_hidden(X5,sK3(X0,X5,X6))
            & v3_pre_topc(X8,X0)
            & v3_pre_topc(sK3(X0,X5,X6),X0)
            & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X6,X5,X0] :
      ( ? [X8] :
          ( r1_xboole_0(sK3(X0,X5,X6),X8)
          & r1_tarski(X6,X8)
          & r2_hidden(X5,sK3(X0,X5,X6))
          & v3_pre_topc(X8,X0)
          & v3_pre_topc(sK3(X0,X5,X6),X0)
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(sK3(X0,X5,X6),sK4(X0,X5,X6))
        & r1_tarski(X6,sK4(X0,X5,X6))
        & r2_hidden(X5,sK3(X0,X5,X6))
        & v3_pre_topc(sK4(X0,X5,X6),X0)
        & v3_pre_topc(sK3(X0,X5,X6),X0)
        & m1_subset_1(sK4(X0,X5,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( ~ r1_xboole_0(X3,X4)
                          | ~ r1_tarski(X2,X4)
                          | ~ r2_hidden(X1,X3)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ v3_pre_topc(X3,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                  & v4_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( r1_xboole_0(X7,X8)
                          & r1_tarski(X6,X8)
                          & r2_hidden(X5,X7)
                          & v3_pre_topc(X8,X0)
                          & v3_pre_topc(X7,X0)
                          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X5,k3_subset_1(u1_struct_0(X0),X6))
                  | ~ v4_pre_topc(X6,X0)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v9_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( ~ r1_xboole_0(X3,X4)
                          | ~ r1_tarski(X2,X4)
                          | ~ r2_hidden(X1,X3)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ v3_pre_topc(X3,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                  & v4_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( r1_xboole_0(X3,X4)
                          & r1_tarski(X2,X4)
                          & r2_hidden(X1,X3)
                          & v3_pre_topc(X4,X0)
                          & v3_pre_topc(X3,X0)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                  | ~ v4_pre_topc(X2,X0)
                  | k1_xboole_0 = X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( r1_xboole_0(X3,X4)
                        & r1_tarski(X2,X4)
                        & r2_hidden(X1,X3)
                        & v3_pre_topc(X4,X0)
                        & v3_pre_topc(X3,X0)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                | ~ v4_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_pre_topc(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ! [X4] :
                            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                           => ~ ( r1_xboole_0(X3,X4)
                                & r1_tarski(X2,X4)
                                & r2_hidden(X1,X3)
                                & v3_pre_topc(X4,X0)
                                & v3_pre_topc(X3,X0) ) ) )
                    & r2_hidden(X1,k3_subset_1(u1_struct_0(X0),X2))
                    & v4_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_compts_1)).

fof(f376,plain,
    ( v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f374])).

fof(f392,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_5
    | ~ spl8_21
    | spl8_6
    | ~ spl8_3
    | spl8_50
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f345,f109,f389,f85,f99,f241,f94,f169,f81,f77])).

fof(f169,plain,
    ( spl8_12
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f94,plain,
    ( spl8_5
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f241,plain,
    ( spl8_21
  <=> v2_compts_1(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f99,plain,
    ( spl8_6
  <=> sQ7_eqProxy(k1_xboole_0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f345,plain,
    ( m1_subset_1(sK5(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | sQ7_eqProxy(k1_xboole_0,sK2(sK0))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f111,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_xboole_0,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f46,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2))
                & r1_tarski(X1,sK6(X0,X1,X2))
                & r2_hidden(X2,sK5(X0,X1,X2))
                & v3_pre_topc(sK6(X0,X1,X2),X0)
                & v3_pre_topc(sK5(X0,X1,X2),X0)
                & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( r1_xboole_0(X3,X4)
              & r1_tarski(X1,X4)
              & r2_hidden(X2,X3)
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X4] :
            ( r1_xboole_0(sK5(X0,X1,X2),X4)
            & r1_tarski(X1,X4)
            & r2_hidden(X2,sK5(X0,X1,X2))
            & v3_pre_topc(X4,X0)
            & v3_pre_topc(sK5(X0,X1,X2),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(sK5(X0,X1,X2),X4)
          & r1_tarski(X1,X4)
          & r2_hidden(X2,sK5(X0,X1,X2))
          & v3_pre_topc(X4,X0)
          & v3_pre_topc(sK5(X0,X1,X2),X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2))
        & r1_tarski(X1,sK6(X0,X1,X2))
        & r2_hidden(X2,sK5(X0,X1,X2))
        & v3_pre_topc(sK6(X0,X1,X2),X0)
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X1,X4)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( r1_xboole_0(X3,X4)
                      & r1_tarski(X1,X4)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X4,X0)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | k1_xboole_0 = X1
          | ~ v2_compts_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v8_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_compts_1(X1,X0)
             => ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ ( ! [X3] :
                            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                           => ! [X4] :
                                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_xboole_0(X3,X4)
                                    & r1_tarski(X1,X4)
                                    & r2_hidden(X2,X3)
                                    & v3_pre_topc(X4,X0)
                                    & v3_pre_topc(X3,X0) ) ) )
                        & r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1)) ) )
                | k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_compts_1)).

fof(f111,plain,
    ( r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f387,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_5
    | ~ spl8_21
    | spl8_6
    | ~ spl8_3
    | spl8_49
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f344,f109,f384,f85,f99,f241,f94,f169,f81,f77])).

fof(f344,plain,
    ( m1_subset_1(sK6(sK0,sK2(sK0),sK1(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | sQ7_eqProxy(k1_xboole_0,sK2(sK0))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f111,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_xboole_0,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f47,f53])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f382,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_5
    | ~ spl8_21
    | spl8_6
    | ~ spl8_3
    | spl8_48
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f343,f109,f379,f85,f99,f241,f94,f169,f81,f77])).

fof(f343,plain,
    ( v3_pre_topc(sK5(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | sQ7_eqProxy(k1_xboole_0,sK2(sK0))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f111,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_xboole_0,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f48,f53])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f377,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_5
    | ~ spl8_21
    | spl8_6
    | ~ spl8_3
    | spl8_47
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f342,f109,f374,f85,f99,f241,f94,f169,f81,f77])).

fof(f342,plain,
    ( v3_pre_topc(sK6(sK0,sK2(sK0),sK1(sK0)),sK0)
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | sQ7_eqProxy(k1_xboole_0,sK2(sK0))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f111,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_xboole_0,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f49,f53])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f372,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_5
    | ~ spl8_21
    | spl8_6
    | ~ spl8_3
    | spl8_46
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f341,f109,f369,f85,f99,f241,f94,f169,f81,f77])).

fof(f341,plain,
    ( r2_hidden(sK1(sK0),sK5(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | sQ7_eqProxy(k1_xboole_0,sK2(sK0))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f111,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK5(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_xboole_0,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f50,f53])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK5(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f367,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_5
    | ~ spl8_21
    | spl8_6
    | ~ spl8_3
    | spl8_45
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f340,f109,f364,f85,f99,f241,f94,f169,f81,f77])).

fof(f340,plain,
    ( r1_tarski(sK2(sK0),sK6(sK0,sK2(sK0),sK1(sK0)))
    | ~ m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | sQ7_eqProxy(k1_xboole_0,sK2(sK0))
    | ~ v2_compts_1(sK2(sK0),sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f111,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_xboole_0,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f51,f53])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f313,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_21
    | spl8_6
    | spl8_34
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f283,f94,f311,f99,f241,f169,f81,f77])).

fof(f283,plain,
    ( ! [X2] :
        ( r1_xboole_0(sK5(sK0,sK2(sK0),X2),sK6(sK0,sK2(sK0),X2))
        | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sQ7_eqProxy(k1_xboole_0,sK2(sK0))
        | ~ v2_compts_1(sK2(sK0),sK0)
        | ~ v8_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f96,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_xboole_0,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f52,f53])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK5(X0,X1,X2),sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f244,plain,
    ( ~ spl8_2
    | ~ spl8_5
    | ~ spl8_10
    | spl8_21
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f239,f104,f241,f145,f94,f81])).

fof(f145,plain,
    ( spl8_10
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f104,plain,
    ( spl8_7
  <=> v4_pre_topc(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f239,plain,
    ( v2_compts_1(sK2(sK0),sK0)
    | ~ v1_compts_1(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f106,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

fof(f106,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f231,plain,(
    ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl8_20 ),
    inference(resolution,[],[f203,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ v9_pre_topc(sK0)
    & v1_compts_1(sK0)
    & v8_pre_topc(sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ~ v9_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v9_pre_topc(sK0)
      & v1_compts_1(sK0)
      & v8_pre_topc(sK0)
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ~ v9_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ( v1_compts_1(X0)
            & v8_pre_topc(X0) )
         => v9_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ( v1_compts_1(X0)
          & v8_pre_topc(X0) )
       => v9_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_compts_1)).

fof(f203,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f229,plain,(
    spl8_12 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl8_12 ),
    inference(resolution,[],[f171,f29])).

fof(f29,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f171,plain,
    ( ~ v8_pre_topc(sK0)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f227,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl8_10 ),
    inference(resolution,[],[f147,f30])).

fof(f30,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f147,plain,
    ( ~ v1_compts_1(sK0)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f225,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl8_4 ),
    inference(resolution,[],[f91,f31])).

fof(f31,plain,(
    ~ v9_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( v9_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f215,plain,
    ( spl8_20
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f160,f85,f81,f77,f201])).

fof(f160,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v9_pre_topc(X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f214,plain,
    ( spl8_20
    | ~ spl8_1
    | ~ spl8_2
    | spl8_5 ),
    inference(avatar_split_clause,[],[f161,f94,f81,f77,f201])).

fof(f161,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v9_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f213,plain,
    ( spl8_20
    | ~ spl8_1
    | ~ spl8_2
    | spl8_7 ),
    inference(avatar_split_clause,[],[f163,f104,f81,f77,f201])).

fof(f163,plain,
    ( v4_pre_topc(sK2(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v9_pre_topc(X0)
      | v4_pre_topc(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f212,plain,
    ( spl8_20
    | ~ spl8_1
    | ~ spl8_2
    | spl8_8 ),
    inference(avatar_split_clause,[],[f164,f109,f81,f77,f201])).

fof(f164,plain,
    ( r2_hidden(sK1(sK0),k3_subset_1(u1_struct_0(sK0),sK2(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v9_pre_topc(X0)
      | r2_hidden(sK1(X0),k3_subset_1(u1_struct_0(X0),sK2(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f210,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl8_2 ),
    inference(resolution,[],[f83,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,
    ( ~ l1_pre_topc(sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f167,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f79,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,
    ( ~ v2_pre_topc(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f102,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_4 ),
    inference(avatar_split_clause,[],[f72,f89,f99,f81,f77])).

fof(f72,plain,
    ( v9_pre_topc(sK0)
    | ~ sQ7_eqProxy(k1_xboole_0,sK2(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f26,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v9_pre_topc(X0)
      | ~ sQ7_eqProxy(k1_xboole_0,sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f42,f53])).

fof(f42,plain,(
    ! [X0] :
      ( v9_pre_topc(X0)
      | k1_xboole_0 != sK2(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
