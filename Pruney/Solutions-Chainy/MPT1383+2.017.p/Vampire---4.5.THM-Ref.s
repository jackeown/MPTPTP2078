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
% DateTime   : Thu Dec  3 13:15:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 951 expanded)
%              Number of leaves         :   62 ( 462 expanded)
%              Depth                    :   10
%              Number of atoms          : 1164 (5561 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f113,f118,f123,f137,f141,f145,f149,f153,f157,f161,f165,f172,f176,f180,f188,f189,f198,f203,f204,f213,f218,f223,f228,f242,f251,f256,f261,f272,f273,f282,f283,f284,f285,f286,f287,f295,f297,f315,f320,f325,f330,f335,f340,f345,f346,f347,f348,f359,f364,f369,f375,f376,f381,f382,f383])).

fof(f383,plain,
    ( spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f236,f220,f120,f115,f110,f105,f100,f72])).

fof(f72,plain,
    ( spl7_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f100,plain,
    ( spl7_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f105,plain,
    ( spl7_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f110,plain,
    ( spl7_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f115,plain,
    ( spl7_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f120,plain,
    ( spl7_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f220,plain,
    ( spl7_28
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f236,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f122,f117,f112,f107,f102,f222,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f222,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f107,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f122,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f382,plain,
    ( ~ spl7_28
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f298,f120,f115,f110,f105,f100,f72,f220])).

fof(f298,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f122,f117,f112,f107,f102,f74,f55])).

fof(f74,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f381,plain,
    ( spl7_46
    | ~ spl7_32
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f372,f342,f253,f378])).

fof(f378,plain,
    ( spl7_46
  <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f253,plain,
    ( spl7_32
  <=> r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f342,plain,
    ( spl7_42
  <=> r1_tarski(k1_tops_1(sK0,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f372,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl7_32
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f344,f254,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f254,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f253])).

fof(f344,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),sK3)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f342])).

fof(f376,plain,
    ( spl7_34
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f373,f253,f269])).

fof(f269,plain,
    ( spl7_34
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f373,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f254,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f375,plain,
    ( ~ spl7_30
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_27
    | spl7_28
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f374,f253,f220,f215,f115,f110,f95,f90,f80,f239])).

fof(f239,plain,
    ( spl7_30
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f80,plain,
    ( spl7_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f90,plain,
    ( spl7_5
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f95,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f215,plain,
    ( spl7_27
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f374,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_27
    | spl7_28
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f117,f112,f82,f92,f221,f217,f97,f254,f60])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X5,X6)
      | ~ r1_tarski(X6,X1)
      | ~ v3_pre_topc(X6,X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( ~ r2_hidden(sK4(X0,X1),X3)
                      | ~ r1_tarski(X3,X1)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK4(X0,X1),X1) )
                & ( ( r2_hidden(sK4(X0,X1),sK5(X0,X1))
                    & r1_tarski(sK5(X0,X1),X1)
                    & v3_pre_topc(sK5(X0,X1),X0)
                    & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK4(X0,X1),X1) ) ) )
            & ( ! [X5] :
                  ( ( r2_hidden(X5,X1)
                    | ! [X6] :
                        ( ~ r2_hidden(X5,X6)
                        | ~ r1_tarski(X6,X1)
                        | ~ v3_pre_topc(X6,X0)
                        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  & ( ( r2_hidden(X5,sK6(X0,X1,X5))
                      & r1_tarski(sK6(X0,X1,X5),X1)
                      & v3_pre_topc(sK6(X0,X1,X5),X0)
                      & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X5,X1) ) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
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
     => ( ( ! [X3] :
              ( ~ r2_hidden(sK4(X0,X1),X3)
              | ~ r1_tarski(X3,X1)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(sK4(X0,X1),X4)
              & r1_tarski(X4,X1)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(sK4(X0,X1),X4)
          & r1_tarski(X4,X1)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(sK4(X0,X1),sK5(X0,X1))
        & r1_tarski(sK5(X0,X1),X1)
        & v3_pre_topc(sK5(X0,X1),X0)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( r2_hidden(X5,X7)
          & r1_tarski(X7,X1)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X5,sK6(X0,X1,X5))
        & r1_tarski(sK6(X0,X1,X5),X1)
        & v3_pre_topc(sK6(X0,X1,X5),X0)
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
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
                    | r2_hidden(X2,X1) ) ) )
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
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
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
                    | r2_hidden(X2,X1) ) ) )
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
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f97,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f217,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f215])).

fof(f221,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl7_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f92,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f82,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f369,plain,
    ( spl7_45
    | ~ spl7_4
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f352,f342,f85,f366])).

fof(f366,plain,
    ( spl7_45
  <=> r1_tarski(k1_tops_1(sK0,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f85,plain,
    ( spl7_4
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f352,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),sK2)
    | ~ spl7_4
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f87,f344,f70])).

fof(f87,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f364,plain,
    ( spl7_44
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f353,f342,f195,f361])).

fof(f361,plain,
    ( spl7_44
  <=> r1_tarski(k1_tops_1(sK0,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f195,plain,
    ( spl7_24
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f353,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),u1_struct_0(sK0))
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f196,f344,f70])).

fof(f196,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f359,plain,
    ( spl7_43
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f354,f342,f356])).

fof(f356,plain,
    ( spl7_43
  <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f354,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(sK3))
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f344,f69])).

fof(f348,plain,
    ( spl7_39
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f299,f135,f95,f90,f80,f327])).

fof(f327,plain,
    ( spl7_39
  <=> v3_pre_topc(sK6(sK0,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f135,plain,
    ( spl7_12
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X3,X4)
        | v3_pre_topc(sK6(sK0,X4,X3),sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f299,plain,
    ( v3_pre_topc(sK6(sK0,sK3,sK1),sK0)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f82,f92,f97,f136])).

fof(f136,plain,
    ( ! [X4,X3] :
        ( v3_pre_topc(sK6(sK0,X4,X3),sK0)
        | ~ r2_hidden(X3,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X4,sK0) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f347,plain,
    ( spl7_36
    | ~ spl7_6
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f300,f163,f95,f312])).

fof(f312,plain,
    ( spl7_36
  <=> v3_pre_topc(k1_tops_1(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f163,plain,
    ( spl7_19
  <=> ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k1_tops_1(sK0,X16),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f300,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK3),sK0)
    | ~ spl7_6
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f97,f164])).

fof(f164,plain,
    ( ! [X16] :
        ( v3_pre_topc(k1_tops_1(sK0,X16),sK0)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f346,plain,
    ( spl7_42
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f301,f110,f95,f342])).

fof(f301,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),sK3)
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f97,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f345,plain,
    ( spl7_42
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f302,f110,f95,f342])).

fof(f302,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),sK3)
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f112,f97,f52])).

fof(f340,plain,
    ( ~ spl7_41
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11
    | spl7_25 ),
    inference(avatar_split_clause,[],[f304,f200,f120,f115,f110,f105,f95,f337])).

fof(f337,plain,
    ( spl7_41
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f200,plain,
    ( spl7_25
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f304,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11
    | spl7_25 ),
    inference(unit_resulting_resolution,[],[f122,f117,f112,f202,f107,f97,f55])).

fof(f202,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f335,plain,
    ( spl7_40
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f305,f115,f110,f95,f90,f80,f332])).

fof(f332,plain,
    ( spl7_40
  <=> m1_subset_1(sK6(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f305,plain,
    ( m1_subset_1(sK6(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f117,f112,f82,f92,f97,f56])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f330,plain,
    ( spl7_39
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f306,f115,f110,f95,f90,f80,f327])).

fof(f306,plain,
    ( v3_pre_topc(sK6(sK0,sK3,sK1),sK0)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f117,f82,f112,f92,f97,f57])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X5,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK6(X0,X1,X5),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f325,plain,
    ( spl7_38
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f307,f115,f110,f95,f90,f80,f322])).

fof(f322,plain,
    ( spl7_38
  <=> r1_tarski(sK6(sK0,sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f307,plain,
    ( r1_tarski(sK6(sK0,sK3,sK1),sK3)
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f117,f82,f112,f92,f97,f58])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X5,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK6(X0,X1,X5),X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f320,plain,
    ( spl7_37
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f308,f115,f110,f95,f90,f80,f317])).

fof(f317,plain,
    ( spl7_37
  <=> r2_hidden(sK1,sK6(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f308,plain,
    ( r2_hidden(sK1,sK6(sK0,sK3,sK1))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f117,f82,f112,f92,f97,f59])).

fof(f59,plain,(
    ! [X0,X5,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X5,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,sK6(X0,X1,X5))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f315,plain,
    ( spl7_36
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f309,f115,f110,f95,f312])).

fof(f309,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK3),sK0)
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f117,f112,f97,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f297,plain,
    ( ~ spl7_6
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | spl7_32 ),
    inference(avatar_split_clause,[],[f296,f253,f110,f100,f90,f85,f95])).

fof(f296,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_9
    | spl7_32 ),
    inference(unit_resulting_resolution,[],[f112,f87,f255,f102,f92,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
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
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f255,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | spl7_32 ),
    inference(avatar_component_clause,[],[f253])).

fof(f295,plain,
    ( ~ spl7_35
    | ~ spl7_4
    | spl7_32 ),
    inference(avatar_split_clause,[],[f288,f253,f85,f292])).

fof(f292,plain,
    ( spl7_35
  <=> r1_tarski(sK2,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f288,plain,
    ( ~ r1_tarski(sK2,k1_tops_1(sK0,sK2))
    | ~ spl7_4
    | spl7_32 ),
    inference(unit_resulting_resolution,[],[f255,f87,f70])).

fof(f287,plain,
    ( ~ spl7_6
    | spl7_24 ),
    inference(avatar_split_clause,[],[f231,f195,f95])).

fof(f231,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_24 ),
    inference(unit_resulting_resolution,[],[f197,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f197,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | spl7_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f286,plain,
    ( ~ spl7_6
    | spl7_24 ),
    inference(avatar_split_clause,[],[f233,f195,f95])).

fof(f233,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_24 ),
    inference(resolution,[],[f197,f68])).

fof(f285,plain,
    ( ~ spl7_4
    | spl7_23 ),
    inference(avatar_split_clause,[],[f229,f185,f85])).

fof(f185,plain,
    ( spl7_23
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f229,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl7_23 ),
    inference(unit_resulting_resolution,[],[f187,f69])).

fof(f187,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f284,plain,
    ( ~ spl7_4
    | spl7_23 ),
    inference(avatar_split_clause,[],[f230,f185,f85])).

fof(f230,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl7_23 ),
    inference(resolution,[],[f187,f69])).

fof(f283,plain,
    ( ~ spl7_4
    | spl7_24
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f234,f210,f195,f85])).

fof(f210,plain,
    ( spl7_26
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f234,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl7_24
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f197,f212,f70])).

fof(f212,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f210])).

fof(f282,plain,
    ( spl7_30
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f281,f258,f239])).

fof(f258,plain,
    ( spl7_33
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f281,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f260,f69])).

fof(f260,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f273,plain,
    ( ~ spl7_34
    | spl7_32 ),
    inference(avatar_split_clause,[],[f267,f253,f269])).

fof(f267,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | spl7_32 ),
    inference(resolution,[],[f255,f68])).

fof(f272,plain,
    ( ~ spl7_34
    | spl7_32 ),
    inference(avatar_split_clause,[],[f265,f253,f269])).

fof(f265,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | spl7_32 ),
    inference(unit_resulting_resolution,[],[f255,f68])).

fof(f261,plain,
    ( spl7_33
    | ~ spl7_26
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f244,f225,f210,f258])).

fof(f225,plain,
    ( spl7_29
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f244,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl7_26
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f212,f227,f70])).

fof(f227,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f225])).

fof(f256,plain,
    ( ~ spl7_32
    | spl7_4
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f245,f225,f85,f253])).

fof(f245,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | spl7_4
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f86,f227,f70])).

fof(f86,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f251,plain,
    ( spl7_31
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f246,f225,f248])).

fof(f248,plain,
    ( spl7_31
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f246,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2))
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f227,f69])).

fof(f242,plain,
    ( ~ spl7_29
    | ~ spl7_27
    | ~ spl7_30
    | ~ spl7_2
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f237,f220,f76,f239,f215,f225])).

fof(f76,plain,
    ( spl7_2
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f237,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl7_2
    | ~ spl7_28 ),
    inference(resolution,[],[f222,f77])).

fof(f77,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f228,plain,
    ( spl7_29
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f205,f110,f100,f225])).

fof(f205,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f112,f102,f52])).

fof(f223,plain,
    ( spl7_28
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f206,f120,f115,f110,f105,f100,f72,f220])).

fof(f206,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f122,f117,f112,f73,f107,f102,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f218,plain,
    ( spl7_27
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f207,f115,f110,f100,f215])).

fof(f207,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f117,f112,f102,f67])).

fof(f213,plain,
    ( spl7_26
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f208,f100,f210])).

fof(f208,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f102,f68])).

fof(f204,plain,
    ( ~ spl7_24
    | spl7_6 ),
    inference(avatar_split_clause,[],[f193,f95,f195])).

fof(f193,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | spl7_6 ),
    inference(resolution,[],[f96,f69])).

fof(f96,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f203,plain,
    ( ~ spl7_25
    | spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f191,f120,f115,f110,f105,f95,f200])).

fof(f191,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | spl7_6
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f122,f117,f112,f107,f96,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f198,plain,
    ( ~ spl7_24
    | spl7_6 ),
    inference(avatar_split_clause,[],[f192,f95,f195])).

fof(f192,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f96,f69])).

fof(f189,plain,
    ( ~ spl7_23
    | spl7_4 ),
    inference(avatar_split_clause,[],[f183,f85,f185])).

fof(f183,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | spl7_4 ),
    inference(resolution,[],[f86,f68])).

fof(f188,plain,
    ( ~ spl7_23
    | spl7_4 ),
    inference(avatar_split_clause,[],[f181,f85,f185])).

fof(f181,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f86,f68])).

fof(f180,plain,
    ( ~ spl7_10
    | ~ spl7_9
    | spl7_22
    | spl7_11 ),
    inference(avatar_split_clause,[],[f168,f120,f178,f110,f115])).

fof(f178,plain,
    ( spl7_22
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,k1_tops_1(sK0,X5))
        | m1_connsp_2(X5,sK0,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f168,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k1_tops_1(sK0,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(X5,sK0,X4) )
    | spl7_11 ),
    inference(resolution,[],[f122,f55])).

fof(f176,plain,
    ( ~ spl7_10
    | ~ spl7_9
    | spl7_21
    | spl7_11 ),
    inference(avatar_split_clause,[],[f167,f120,f174,f110,f115])).

fof(f174,plain,
    ( spl7_21
  <=> ! [X3,X2] :
        ( ~ m1_connsp_2(X2,sK0,X3)
        | r2_hidden(X3,k1_tops_1(sK0,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f167,plain,
    ( ! [X2,X3] :
        ( ~ m1_connsp_2(X2,sK0,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | r2_hidden(X3,k1_tops_1(sK0,X2)) )
    | spl7_11 ),
    inference(resolution,[],[f122,f54])).

fof(f172,plain,
    ( ~ spl7_10
    | ~ spl7_9
    | spl7_20
    | spl7_11 ),
    inference(avatar_split_clause,[],[f166,f120,f170,f110,f115])).

fof(f170,plain,
    ( spl7_20
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_11 ),
    inference(resolution,[],[f122,f66])).

fof(f165,plain,
    ( ~ spl7_10
    | spl7_19
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f133,f110,f163,f115])).

fof(f133,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k1_tops_1(sK0,X16),sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f67])).

fof(f161,plain,
    ( ~ spl7_10
    | spl7_18
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f132,f110,f159,f115])).

fof(f159,plain,
    ( spl7_18
  <=> ! [X15,X14] :
        ( ~ r2_hidden(sK4(sK0,X14),X15)
        | v3_pre_topc(X14,sK0)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK4(sK0,X14),X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X15,sK0)
        | ~ r1_tarski(X15,X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f132,plain,
    ( ! [X14,X15] :
        ( ~ r2_hidden(sK4(sK0,X14),X15)
        | ~ r1_tarski(X15,X14)
        | ~ v3_pre_topc(X15,sK0)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK4(sK0,X14),X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X14,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(sK4(X0,X1),X3)
      | ~ r1_tarski(X3,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f157,plain,
    ( ~ spl7_10
    | spl7_17
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f131,f110,f155,f115])).

fof(f155,plain,
    ( spl7_17
  <=> ! [X13] :
        ( r1_tarski(sK5(sK0,X13),X13)
        | v3_pre_topc(X13,sK0)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK4(sK0,X13),X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f131,plain,
    ( ! [X13] :
        ( r1_tarski(sK5(sK0,X13),X13)
        | r2_hidden(sK4(sK0,X13),X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X13,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK5(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f153,plain,
    ( ~ spl7_10
    | spl7_16
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f130,f110,f151,f115])).

fof(f151,plain,
    ( spl7_16
  <=> ! [X12] :
        ( v3_pre_topc(sK5(sK0,X12),sK0)
        | v3_pre_topc(X12,sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK4(sK0,X12),X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f130,plain,
    ( ! [X12] :
        ( v3_pre_topc(sK5(sK0,X12),sK0)
        | r2_hidden(sK4(sK0,X12),X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X12,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v3_pre_topc(sK5(X0,X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f149,plain,
    ( ~ spl7_10
    | spl7_15
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f129,f110,f147,f115])).

fof(f147,plain,
    ( spl7_15
  <=> ! [X9,X11,X10] :
        ( ~ r2_hidden(X9,X10)
        | r2_hidden(X9,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X11,sK0)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X10,sK0)
        | ~ r1_tarski(X10,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f129,plain,
    ( ! [X10,X11,X9] :
        ( ~ r2_hidden(X9,X10)
        | ~ r1_tarski(X10,X11)
        | ~ v3_pre_topc(X10,sK0)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X11,sK0)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X9,X11)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f60])).

fof(f145,plain,
    ( ~ spl7_10
    | spl7_14
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f128,f110,f143,f115])).

fof(f143,plain,
    ( spl7_14
  <=> ! [X7,X8] :
        ( ~ r2_hidden(X7,X8)
        | r2_hidden(X7,sK6(sK0,X8,X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X8,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f128,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(X7,X8)
        | ~ v3_pre_topc(X8,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X7,sK6(sK0,X8,X7))
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f59])).

fof(f141,plain,
    ( ~ spl7_10
    | spl7_13
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f127,f110,f139,f115])).

fof(f139,plain,
    ( spl7_13
  <=> ! [X5,X6] :
        ( ~ r2_hidden(X5,X6)
        | r1_tarski(sK6(sK0,X6,X5),X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X6,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f127,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,X6)
        | ~ v3_pre_topc(X6,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK6(sK0,X6,X5),X6)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f58])).

fof(f137,plain,
    ( ~ spl7_10
    | spl7_12
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f126,f110,f135,f115])).

fof(f126,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,X4)
        | ~ v3_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK6(sK0,X4,X3),sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f112,f57])).

fof(f123,plain,(
    ~ spl7_11 ),
    inference(avatar_split_clause,[],[f42,f120])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | m1_connsp_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | m1_connsp_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ m1_connsp_2(X2,sK0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | m1_connsp_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ m1_connsp_2(X2,sK0,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,sK0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | m1_connsp_2(X2,sK0,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(sK1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ m1_connsp_2(X2,sK0,sK1) )
          & ( ? [X4] :
                ( r2_hidden(sK1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | m1_connsp_2(X2,sK0,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(sK1,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ m1_connsp_2(X2,sK0,sK1) )
        & ( ? [X4] :
              ( r2_hidden(sK1,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | m1_connsp_2(X2,sK0,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK1,X3)
            | ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ m1_connsp_2(sK2,sK0,sK1) )
      & ( ? [X4] :
            ( r2_hidden(sK1,X4)
            & r1_tarski(X4,sK2)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | m1_connsp_2(sK2,sK0,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( r2_hidden(sK1,X4)
        & r1_tarski(X4,sK2)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,sK3)
      & r1_tarski(sK3,sK2)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X4] :
                    ( r2_hidden(X1,X4)
                    & r1_tarski(X4,X2)
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X1,X3)
                    | ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
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
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f118,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f43,f115])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f44,f110])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f45,f105])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f46,f100])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f47,f95,f72])).

fof(f47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,
    ( spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f48,f90,f72])).

fof(f48,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f49,f85,f72])).

fof(f49,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f50,f80,f72])).

fof(f50,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f51,f76,f72])).

fof(f51,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f33])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (17325)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.46  % (17327)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (17319)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (17325)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f113,f118,f123,f137,f141,f145,f149,f153,f157,f161,f165,f172,f176,f180,f188,f189,f198,f203,f204,f213,f218,f223,f228,f242,f251,f256,f261,f272,f273,f282,f283,f284,f285,f286,f287,f295,f297,f315,f320,f325,f330,f335,f340,f345,f346,f347,f348,f359,f364,f369,f375,f376,f381,f382,f383])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11 | ~spl7_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f236,f220,f120,f115,f110,f105,f100,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl7_1 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl7_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl7_8 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl7_9 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl7_10 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl7_11 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    spl7_28 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    m1_connsp_2(sK2,sK0,sK1) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11 | ~spl7_28)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f122,f117,f112,f107,f102,f222,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl7_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f220])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f105])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl7_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f110])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl7_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f115])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl7_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f120])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    ~spl7_28 | spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f298,f120,f115,f110,f105,f100,f72,f220])).
% 0.21/0.48  fof(f298,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f122,f117,f112,f107,f102,f74,f55])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~m1_connsp_2(sK2,sK0,sK1) | spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    spl7_46 | ~spl7_32 | ~spl7_42),
% 0.21/0.48    inference(avatar_split_clause,[],[f372,f342,f253,f378])).
% 0.21/0.48  fof(f378,plain,(
% 0.21/0.48    spl7_46 <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    spl7_32 <=> r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    spl7_42 <=> r1_tarski(k1_tops_1(sK0,sK3),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | (~spl7_32 | ~spl7_42)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f344,f254,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    r1_tarski(sK3,k1_tops_1(sK0,sK2)) | ~spl7_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f253])).
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK3),sK3) | ~spl7_42),
% 0.21/0.48    inference(avatar_component_clause,[],[f342])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    spl7_34 | ~spl7_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f373,f253,f269])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    spl7_34 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~spl7_32),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f254,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    ~spl7_30 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10 | ~spl7_27 | spl7_28 | ~spl7_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f374,f253,f220,f215,f115,f110,f95,f90,f80,f239])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl7_30 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl7_3 <=> r2_hidden(sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl7_5 <=> v3_pre_topc(sK3,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    spl7_27 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10 | ~spl7_27 | spl7_28 | ~spl7_32)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f117,f112,f82,f92,f221,f217,f97,f254,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X6,X0,X5,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X5,X6) | ~r1_tarski(X6,X1) | ~v3_pre_topc(X6,X0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ((! [X3] : (~r2_hidden(sK4(X0,X1),X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),X1)) & ((r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r1_tarski(sK5(X0,X1),X1) & v3_pre_topc(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X1) | ~v3_pre_topc(X6,X0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X5,sK6(X0,X1,X5)) & r1_tarski(sK6(X0,X1,X5),X1) & v3_pre_topc(sK6(X0,X1,X5),X0) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(sK4(X0,X1),X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (r2_hidden(sK4(X0,X1),X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X4] : (r2_hidden(sK4(X0,X1),X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r1_tarski(sK5(X0,X1),X1) & v3_pre_topc(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X5,X1,X0] : (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X1) & v3_pre_topc(X7,X0) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X5,sK6(X0,X1,X5)) & r1_tarski(sK6(X0,X1,X5),X1) & v3_pre_topc(sK6(X0,X1,X5),X0) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X2,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X5,X6) | ~r1_tarski(X6,X1) | ~v3_pre_topc(X6,X0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (r2_hidden(X5,X7) & r1_tarski(X7,X1) & v3_pre_topc(X7,X0) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(rectify,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X2,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_1)).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~spl7_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f215])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl7_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f220])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    v3_pre_topc(sK3,sK0) | ~spl7_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    r2_hidden(sK1,sK3) | ~spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    spl7_45 | ~spl7_4 | ~spl7_42),
% 0.21/0.48    inference(avatar_split_clause,[],[f352,f342,f85,f366])).
% 0.21/0.48  fof(f366,plain,(
% 0.21/0.48    spl7_45 <=> r1_tarski(k1_tops_1(sK0,sK3),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl7_4 <=> r1_tarski(sK3,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK3),sK2) | (~spl7_4 | ~spl7_42)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f87,f344,f70])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    r1_tarski(sK3,sK2) | ~spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    spl7_44 | ~spl7_24 | ~spl7_42),
% 0.21/0.48    inference(avatar_split_clause,[],[f353,f342,f195,f361])).
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    spl7_44 <=> r1_tarski(k1_tops_1(sK0,sK3),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    spl7_24 <=> r1_tarski(sK3,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.48  fof(f353,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK3),u1_struct_0(sK0)) | (~spl7_24 | ~spl7_42)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f196,f344,f70])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl7_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f195])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    spl7_43 | ~spl7_42),
% 0.21/0.48    inference(avatar_split_clause,[],[f354,f342,f356])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    spl7_43 <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(sK3)) | ~spl7_42),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f344,f69])).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    spl7_39 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f299,f135,f95,f90,f80,f327])).
% 0.21/0.48  fof(f327,plain,(
% 0.21/0.48    spl7_39 <=> v3_pre_topc(sK6(sK0,sK3,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl7_12 <=> ! [X3,X4] : (~r2_hidden(X3,X4) | v3_pre_topc(sK6(sK0,X4,X3),sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    v3_pre_topc(sK6(sK0,sK3,sK1),sK0) | (~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f82,f92,f97,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X4,X3] : (v3_pre_topc(sK6(sK0,X4,X3),sK0) | ~r2_hidden(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X4,sK0)) ) | ~spl7_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f135])).
% 0.21/0.48  fof(f347,plain,(
% 0.21/0.48    spl7_36 | ~spl7_6 | ~spl7_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f300,f163,f95,f312])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    spl7_36 <=> v3_pre_topc(k1_tops_1(sK0,sK3),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    spl7_19 <=> ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X16),sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    v3_pre_topc(k1_tops_1(sK0,sK3),sK0) | (~spl7_6 | ~spl7_19)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f97,f164])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ( ! [X16] : (v3_pre_topc(k1_tops_1(sK0,X16),sK0) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f163])).
% 0.21/0.48  fof(f346,plain,(
% 0.21/0.48    spl7_42 | ~spl7_6 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f301,f110,f95,f342])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK3),sK3) | (~spl7_6 | ~spl7_9)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f97,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    spl7_42 | ~spl7_6 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f302,f110,f95,f342])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK3),sK3) | (~spl7_6 | ~spl7_9)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f112,f97,f52])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    ~spl7_41 | ~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11 | spl7_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f304,f200,f120,f115,f110,f105,f95,f337])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    spl7_41 <=> r2_hidden(sK1,k1_tops_1(sK0,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    spl7_25 <=> m1_connsp_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.48  fof(f304,plain,(
% 0.21/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | (~spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11 | spl7_25)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f122,f117,f112,f202,f107,f97,f55])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~m1_connsp_2(sK3,sK0,sK1) | spl7_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f200])).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    spl7_40 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f305,f115,f110,f95,f90,f80,f332])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    spl7_40 <=> m1_subset_1(sK6(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    m1_subset_1(sK6(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f117,f112,f82,f92,f97,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X5,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    spl7_39 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f306,f115,f110,f95,f90,f80,f327])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    v3_pre_topc(sK6(sK0,sK3,sK1),sK0) | (~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f117,f82,f112,f92,f97,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X5,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK6(X0,X1,X5),X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    spl7_38 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f307,f115,f110,f95,f90,f80,f322])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    spl7_38 <=> r1_tarski(sK6(sK0,sK3,sK1),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    r1_tarski(sK6(sK0,sK3,sK1),sK3) | (~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f117,f82,f112,f92,f97,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X5,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK6(X0,X1,X5),X1) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    spl7_37 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f308,f115,f110,f95,f90,f80,f317])).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    spl7_37 <=> r2_hidden(sK1,sK6(sK0,sK3,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    r2_hidden(sK1,sK6(sK0,sK3,sK1)) | (~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_9 | ~spl7_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f117,f82,f112,f92,f97,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X5,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,sK6(X0,X1,X5)) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    spl7_36 | ~spl7_6 | ~spl7_9 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f309,f115,f110,f95,f312])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    v3_pre_topc(k1_tops_1(sK0,sK3),sK0) | (~spl7_6 | ~spl7_9 | ~spl7_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f117,f112,f97,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    ~spl7_6 | ~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_9 | spl7_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f296,f253,f110,f100,f90,f85,f95])).
% 0.21/0.48  fof(f296,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_9 | spl7_32)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f112,f87,f255,f102,f92,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ~r1_tarski(sK3,k1_tops_1(sK0,sK2)) | spl7_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f253])).
% 0.21/0.48  fof(f295,plain,(
% 0.21/0.48    ~spl7_35 | ~spl7_4 | spl7_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f288,f253,f85,f292])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    spl7_35 <=> r1_tarski(sK2,k1_tops_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    ~r1_tarski(sK2,k1_tops_1(sK0,sK2)) | (~spl7_4 | spl7_32)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f255,f87,f70])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    ~spl7_6 | spl7_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f231,f195,f95])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_24),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f197,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    ~r1_tarski(sK3,u1_struct_0(sK0)) | spl7_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f195])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    ~spl7_6 | spl7_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f233,f195,f95])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_24),
% 0.21/0.48    inference(resolution,[],[f197,f68])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ~spl7_4 | spl7_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f229,f185,f85])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    spl7_23 <=> m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ~r1_tarski(sK3,sK2) | spl7_23),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f187,f69])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(sK2)) | spl7_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f185])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    ~spl7_4 | spl7_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f230,f185,f85])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ~r1_tarski(sK3,sK2) | spl7_23),
% 0.21/0.48    inference(resolution,[],[f187,f69])).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    ~spl7_4 | spl7_24 | ~spl7_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f234,f210,f195,f85])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    spl7_26 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ~r1_tarski(sK3,sK2) | (spl7_24 | ~spl7_26)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f197,f212,f70])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl7_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f210])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    spl7_30 | ~spl7_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f281,f258,f239])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl7_33 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_33),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f260,f69])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~spl7_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f258])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    ~spl7_34 | spl7_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f267,f253,f269])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | spl7_32),
% 0.21/0.48    inference(resolution,[],[f255,f68])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    ~spl7_34 | spl7_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f265,f253,f269])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | spl7_32),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f255,f68])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    spl7_33 | ~spl7_26 | ~spl7_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f244,f225,f210,f258])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    spl7_29 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | (~spl7_26 | ~spl7_29)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f212,f227,f70])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl7_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f225])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ~spl7_32 | spl7_4 | ~spl7_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f245,f225,f85,f253])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ~r1_tarski(sK3,k1_tops_1(sK0,sK2)) | (spl7_4 | ~spl7_29)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f86,f227,f70])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~r1_tarski(sK3,sK2) | spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    spl7_31 | ~spl7_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f246,f225,f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    spl7_31 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2)) | ~spl7_29),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f227,f69])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~spl7_29 | ~spl7_27 | ~spl7_30 | ~spl7_2 | ~spl7_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f237,f220,f76,f239,f215,f225])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl7_2 <=> ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl7_2 | ~spl7_28)),
% 0.21/0.48    inference(resolution,[],[f222,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2)) ) | ~spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    spl7_29 | ~spl7_7 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f205,f110,f100,f225])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl7_7 | ~spl7_9)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f112,f102,f52])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    spl7_28 | ~spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f206,f120,f115,f110,f105,f100,f72,f220])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (~spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f122,f117,f112,f73,f107,f102,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    m1_connsp_2(sK2,sK0,sK1) | ~spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl7_27 | ~spl7_7 | ~spl7_9 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f207,f115,f110,f100,f215])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | (~spl7_7 | ~spl7_9 | ~spl7_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f117,f112,f102,f67])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl7_26 | ~spl7_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f208,f100,f210])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl7_7),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f102,f68])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ~spl7_24 | spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f193,f95,f195])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ~r1_tarski(sK3,u1_struct_0(sK0)) | spl7_6),
% 0.21/0.48    inference(resolution,[],[f96,f69])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~spl7_25 | spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f191,f120,f115,f110,f105,f95,f200])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~m1_connsp_2(sK3,sK0,sK1) | (spl7_6 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_11)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f122,f117,f112,f107,f96,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~spl7_24 | spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f192,f95,f195])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~r1_tarski(sK3,u1_struct_0(sK0)) | spl7_6),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f96,f69])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~spl7_23 | spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f183,f85,f185])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(sK2)) | spl7_4),
% 0.21/0.48    inference(resolution,[],[f86,f68])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~spl7_23 | spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f181,f85,f185])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(sK2)) | spl7_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f86,f68])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    ~spl7_10 | ~spl7_9 | spl7_22 | spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f168,f120,f178,f110,f115])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl7_22 <=> ! [X5,X4] : (~r2_hidden(X4,k1_tops_1(sK0,X5)) | m1_connsp_2(X5,sK0,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(X5,sK0,X4)) ) | spl7_11),
% 0.21/0.48    inference(resolution,[],[f122,f55])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ~spl7_10 | ~spl7_9 | spl7_21 | spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f167,f120,f174,f110,f115])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    spl7_21 <=> ! [X3,X2] : (~m1_connsp_2(X2,sK0,X3) | r2_hidden(X3,k1_tops_1(sK0,X2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_connsp_2(X2,sK0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_hidden(X3,k1_tops_1(sK0,X2))) ) | spl7_11),
% 0.21/0.48    inference(resolution,[],[f122,f54])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ~spl7_10 | ~spl7_9 | spl7_20 | spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f166,f120,f170,f110,f115])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    spl7_20 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl7_11),
% 0.21/0.48    inference(resolution,[],[f122,f66])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ~spl7_10 | spl7_19 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f133,f110,f163,f115])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X16),sK0) | ~v2_pre_topc(sK0)) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f67])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ~spl7_10 | spl7_18 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f132,f110,f159,f115])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl7_18 <=> ! [X15,X14] : (~r2_hidden(sK4(sK0,X14),X15) | v3_pre_topc(X14,sK0) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X14),X14) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X15,sK0) | ~r1_tarski(X15,X14))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ( ! [X14,X15] : (~r2_hidden(sK4(sK0,X14),X15) | ~r1_tarski(X15,X14) | ~v3_pre_topc(X15,sK0) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK0,X14),X14) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X14,sK0) | ~v2_pre_topc(sK0)) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(sK4(X0,X1),X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~spl7_10 | spl7_17 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f131,f110,f155,f115])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    spl7_17 <=> ! [X13] : (r1_tarski(sK5(sK0,X13),X13) | v3_pre_topc(X13,sK0) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X13),X13))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X13] : (r1_tarski(sK5(sK0,X13),X13) | r2_hidden(sK4(sK0,X13),X13) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X13,sK0) | ~v2_pre_topc(sK0)) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_tarski(sK5(X0,X1),X1) | r2_hidden(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ~spl7_10 | spl7_16 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f130,f110,f151,f115])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl7_16 <=> ! [X12] : (v3_pre_topc(sK5(sK0,X12),sK0) | v3_pre_topc(X12,sK0) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(sK0,X12),X12))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X12] : (v3_pre_topc(sK5(sK0,X12),sK0) | r2_hidden(sK4(sK0,X12),X12) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X12,sK0) | ~v2_pre_topc(sK0)) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | v3_pre_topc(sK5(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~spl7_10 | spl7_15 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f129,f110,f147,f115])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl7_15 <=> ! [X9,X11,X10] : (~r2_hidden(X9,X10) | r2_hidden(X9,X11) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X11,sK0) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X10,sK0) | ~r1_tarski(X10,X11))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (~r2_hidden(X9,X10) | ~r1_tarski(X10,X11) | ~v3_pre_topc(X10,sK0) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X11,sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~v2_pre_topc(sK0)) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f60])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~spl7_10 | spl7_14 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f128,f110,f143,f115])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl7_14 <=> ! [X7,X8] : (~r2_hidden(X7,X8) | r2_hidden(X7,sK6(sK0,X8,X7)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X8,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X8,X7] : (~r2_hidden(X7,X8) | ~v3_pre_topc(X8,sK0) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X7,sK6(sK0,X8,X7)) | ~v2_pre_topc(sK0)) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f59])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~spl7_10 | spl7_13 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f110,f139,f115])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl7_13 <=> ! [X5,X6] : (~r2_hidden(X5,X6) | r1_tarski(sK6(sK0,X6,X5),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X6,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X6,X5] : (~r2_hidden(X5,X6) | ~v3_pre_topc(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK6(sK0,X6,X5),X6) | ~v2_pre_topc(sK0)) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f58])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~spl7_10 | spl7_12 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f126,f110,f135,f115])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~r2_hidden(X3,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK6(sK0,X4,X3),sK0) | ~v2_pre_topc(sK0)) ) | ~spl7_9),
% 0.21/0.48    inference(resolution,[],[f112,f57])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f120])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    (((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f32,f31,f30,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ? [X2] : ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(X2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(X2,sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_connsp_2(sK2,sK0,sK1)) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(rectify,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | m1_connsp_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f115])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f110])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl7_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f105])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl7_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f100])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl7_1 | spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f95,f72])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl7_1 | spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f90,f72])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    v3_pre_topc(sK3,sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl7_1 | spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f85,f72])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    r1_tarski(sK3,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl7_1 | spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f50,f80,f72])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    r2_hidden(sK1,sK3) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~spl7_1 | spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f76,f72])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(sK2,sK0,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17325)------------------------------
% 0.21/0.48  % (17325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17325)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17325)Memory used [KB]: 5628
% 0.21/0.48  % (17325)Time elapsed: 0.077 s
% 0.21/0.48  % (17325)------------------------------
% 0.21/0.48  % (17325)------------------------------
% 0.21/0.48  % (17312)Success in time 0.129 s
%------------------------------------------------------------------------------
