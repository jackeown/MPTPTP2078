%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 769 expanded)
%              Number of leaves         :   30 ( 281 expanded)
%              Depth                    :   24
%              Number of atoms          :  727 (8153 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f81,f85,f89,f109,f157,f159,f161,f185,f200,f221,f279,f334,f350,f356,f400,f429])).

fof(f429,plain,
    ( ~ spl5_4
    | ~ spl5_3
    | ~ spl5_9
    | spl5_38 ),
    inference(avatar_split_clause,[],[f424,f398,f107,f70,f74])).

fof(f74,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f70,plain,
    ( spl5_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f107,plain,
    ( spl5_9
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f398,plain,
    ( spl5_38
  <=> m1_connsp_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f424,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_9
    | spl5_38 ),
    inference(resolution,[],[f410,f399])).

fof(f399,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK2)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f398])).

fof(f410,plain,
    ( ! [X5] :
        ( m1_connsp_2(sK1,sK0,X5)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f99,f108])).

fof(f108,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f99,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_tops_1(sK0,sK1))
      | m1_connsp_2(sK1,sK0,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f37,f38,f39,f93])).

fof(f93,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_tops_1(sK0,sK1))
      | m1_connsp_2(sK1,sK0,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( ! [X3] :
            ( ~ r1_tarski(X3,sK1)
            | ~ m1_connsp_2(X3,sK0,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & r2_hidden(sK2,sK1)
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v3_pre_topc(sK1,sK0) )
    & ( ! [X4] :
          ( ( r1_tarski(sK3(X4),sK1)
            & m1_connsp_2(sK3(X4),sK0,X4)
            & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X4,sK1)
          | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,sK0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v3_pre_topc(X1,sK0) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,sK0,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X1)
                  | ~ m1_connsp_2(X3,sK0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ v3_pre_topc(X1,sK0) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( r1_tarski(X5,X1)
                  & m1_connsp_2(X5,sK0,X4)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,sK1)
                | ~ m1_connsp_2(X3,sK0,X2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & r2_hidden(X2,sK1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ v3_pre_topc(sK1,sK0) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X5,sK1)
                & m1_connsp_2(X5,sK0,X4)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X4,sK1)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X3,sK1)
            | ~ m1_connsp_2(X3,sK0,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ! [X3] :
          ( ~ r1_tarski(X3,sK1)
          | ~ m1_connsp_2(X3,sK0,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4] :
      ( ? [X5] :
          ( r1_tarski(X5,sK1)
          & m1_connsp_2(X5,sK0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
     => ( r1_tarski(sK3(X4),sK1)
        & m1_connsp_2(sK3(X4),sK0,X4)
        & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,X0,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f400,plain,
    ( ~ spl5_38
    | ~ spl5_28
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f396,f66,f270,f398])).

fof(f270,plain,
    ( spl5_28
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f66,plain,
    ( spl5_2
  <=> ! [X3] :
        ( ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f396,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_connsp_2(sK1,sK0,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f67,f40])).

fof(f67,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f356,plain,
    ( spl5_11
    | spl5_9
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f355,f63,f107,f121])).

fof(f121,plain,
    ( spl5_11
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f63,plain,
    ( spl5_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f355,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK1,sK0)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(global_subsumption,[],[f39,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK1,sK0)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f350,plain,
    ( spl5_8
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl5_8
    | spl5_30 ),
    inference(subsumption_resolution,[],[f105,f336])).

fof(f336,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl5_30 ),
    inference(resolution,[],[f333,f57])).

% (6023)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f333,plain,
    ( ~ r2_hidden(sK4(sK1,k1_tops_1(sK0,sK1)),sK1)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl5_30
  <=> r2_hidden(sK4(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

% (6036)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f105,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_8
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f334,plain,
    ( spl5_8
    | ~ spl5_30
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f329,f183,f87,f83,f79,f332,f104])).

fof(f79,plain,
    ( spl5_5
  <=> ! [X4] :
        ( r1_tarski(sK3(X4),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f83,plain,
    ( spl5_6
  <=> ! [X4] :
        ( m1_connsp_2(sK3(X4),sK0,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f87,plain,
    ( spl5_7
  <=> ! [X4] :
        ( m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f183,plain,
    ( spl5_23
  <=> ! [X7,X6] :
        ( ~ r2_hidden(X6,sK1)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,k1_tops_1(sK0,sK3(X6)))
        | ~ m1_connsp_2(sK3(X6),sK0,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f329,plain,
    ( ~ r2_hidden(sK4(sK1,k1_tops_1(sK0,sK1)),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,
    ( ~ r2_hidden(sK4(sK1,k1_tops_1(sK0,sK1)),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(resolution,[],[f312,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f312,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK1,X2),k1_tops_1(sK0,sK1))
        | ~ r2_hidden(sK4(sK1,X2),sK1)
        | r1_tarski(sK1,X2) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( ! [X2] :
        ( r1_tarski(sK1,X2)
        | ~ r2_hidden(sK4(sK1,X2),sK1)
        | r2_hidden(sK4(sK1,X2),k1_tops_1(sK0,sK1))
        | ~ r2_hidden(sK4(sK1,X2),sK1) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(resolution,[],[f298,f96])).

fof(f96,plain,(
    ! [X7] :
      ( m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X7,sK1) ) ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f298,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0)
        | ~ r2_hidden(sK4(sK1,X0),sK1)
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK1)) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | ~ m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK1,X0),sK1)
        | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(resolution,[],[f292,f98])).

fof(f98,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK1,sK0,X4)
      | r2_hidden(X4,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f37,f38,f39,f92])).

fof(f92,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK1,sK0,X4)
      | r2_hidden(X4,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f292,plain,
    ( ! [X2] :
        ( m1_connsp_2(sK1,sK0,sK4(sK1,X2))
        | r1_tarski(sK1,X2)
        | ~ m1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK1,X2),sK1) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(resolution,[],[f280,f230])).

fof(f230,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_tops_1(sK0,sK3(X2)))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_tops_1(sK0,sK3(X2)))
        | ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(resolution,[],[f227,f96])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k1_tops_1(sK0,sK3(X0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k1_tops_1(sK0,sK3(X0)))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(resolution,[],[f184,f163])).

fof(f163,plain,
    ( ! [X4] :
        ( m1_connsp_2(sK3(X4),sK0,X4)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f84,f96])).

fof(f84,plain,
    ( ! [X4] :
        ( m1_connsp_2(sK3(X4),sK0,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f184,plain,
    ( ! [X6,X7] :
        ( ~ m1_connsp_2(sK3(X6),sK0,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,k1_tops_1(sK0,sK3(X6)))
        | ~ r2_hidden(X6,sK1) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f183])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_tops_1(sK0,sK3(sK4(sK1,X0))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_tarski(sK1,X0)
        | m1_connsp_2(sK1,sK0,X1) )
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f265,f209])).

fof(f209,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X2)
      | m1_connsp_2(sK1,sK0,X1) ) ),
    inference(resolution,[],[f99,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f265,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f240,f57])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,X0),sK1)
        | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1))
        | r1_tarski(sK1,X0) )
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f215,f165])).

fof(f165,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(sK4(sK1,X0)),sK1)
        | r1_tarski(sK1,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f164,f57])).

fof(f164,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | r1_tarski(sK3(X4),sK1) )
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f80,f96])).

fof(f80,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_tarski(sK3(X4),sK1)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3(X0),sK1)
        | r1_tarski(k1_tops_1(sK0,sK3(X0)),k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_7 ),
    inference(resolution,[],[f100,f162])).

fof(f162,plain,
    ( ! [X4] :
        ( m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f88,f96])).

fof(f88,plain,
    ( ! [X4] :
        ( m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f100,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X6),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X6,sK1) ) ),
    inference(global_subsumption,[],[f39,f94])).

fof(f94,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,sK1)
      | r1_tarski(k1_tops_1(sK0,X6),k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f279,plain,(
    spl5_28 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl5_28 ),
    inference(resolution,[],[f271,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f271,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f270])).

fof(f221,plain,
    ( ~ spl5_9
    | spl5_1 ),
    inference(avatar_split_clause,[],[f219,f63,f107])).

fof(f219,plain,
    ( v3_pre_topc(sK1,sK0)
    | sK1 != k1_tops_1(sK0,sK1) ),
    inference(global_subsumption,[],[f39,f38,f217])).

fof(f217,plain,
    ( v3_pre_topc(sK1,sK0)
    | sK1 != k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f97,f40])).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2)
      | k1_tops_1(X2,X3) != X3
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(global_subsumption,[],[f39,f91])).

fof(f91,plain,(
    ! [X2,X3] :
      ( k1_tops_1(X2,X3) != X3
      | v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f200,plain,
    ( ~ spl5_10
    | ~ spl5_16
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f198,f121,f138,f118])).

fof(f118,plain,
    ( spl5_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f138,plain,
    ( spl5_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f198,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_11 ),
    inference(resolution,[],[f122,f40])).

fof(f122,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f185,plain,
    ( spl5_15
    | ~ spl5_16
    | ~ spl5_10
    | spl5_23
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f169,f87,f183,f118,f138,f135])).

fof(f135,plain,
    ( spl5_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f169,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK1)
        | ~ m1_connsp_2(sK3(X6),sK0,X7)
        | r2_hidden(X7,k1_tops_1(sK0,sK3(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f162,f49])).

fof(f161,plain,(
    ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f37,f136])).

fof(f136,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f159,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl5_16 ),
    inference(subsumption_resolution,[],[f38,f139])).

fof(f139,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f157,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f39,f119])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f109,plain,
    ( ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f102,f107,f104])).

fof(f102,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f101,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(global_subsumption,[],[f39,f95])).

% (6030)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f95,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f89,plain,
    ( spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f41,f87,f63])).

fof(f41,plain,(
    ! [X4] :
      ( m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f42,f83,f63])).

fof(f42,plain,(
    ! [X4] :
      ( m1_connsp_2(sK3(X4),sK0,X4)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f43,f79,f63])).

fof(f43,plain,(
    ! [X4] :
      ( r1_tarski(sK3(X4),sK1)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f44,f74,f63])).

fof(f44,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f45,f70,f63])).

fof(f45,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f46,f66,f63])).

fof(f46,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:57:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (6011)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (6026)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (6019)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (6011)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (6012)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (6013)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (6027)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (6018)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (6035)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (6032)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (6021)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (6025)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (6037)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (6014)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (6016)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f430,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f68,f72,f76,f81,f85,f89,f109,f157,f159,f161,f185,f200,f221,f279,f334,f350,f356,f400,f429])).
% 0.20/0.53  fof(f429,plain,(
% 0.20/0.53    ~spl5_4 | ~spl5_3 | ~spl5_9 | spl5_38),
% 0.20/0.53    inference(avatar_split_clause,[],[f424,f398,f107,f70,f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    spl5_4 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    spl5_3 <=> r2_hidden(sK2,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl5_9 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.53  fof(f398,plain,(
% 0.20/0.53    spl5_38 <=> m1_connsp_2(sK1,sK0,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.20/0.53  fof(f424,plain,(
% 0.20/0.53    ~r2_hidden(sK2,sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl5_9 | spl5_38)),
% 0.20/0.53    inference(resolution,[],[f410,f399])).
% 0.20/0.53  fof(f399,plain,(
% 0.20/0.53    ~m1_connsp_2(sK1,sK0,sK2) | spl5_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f398])).
% 0.20/0.53  fof(f410,plain,(
% 0.20/0.53    ( ! [X5] : (m1_connsp_2(sK1,sK0,X5) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | ~spl5_9),
% 0.20/0.53    inference(backward_demodulation,[],[f99,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    sK1 = k1_tops_1(sK0,sK1) | ~spl5_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f107])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ( ! [X5] : (~r2_hidden(X5,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 0.20/0.53    inference(global_subsumption,[],[f37,f38,f39,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ( ! [X5] : (~r2_hidden(X5,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f40,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    (((! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & (! [X4] : ((r1_tarski(sK3(X4),sK1) & m1_connsp_2(sK3(X4),sK0,X4) & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28,f27,f26,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ? [X2] : (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X4] : (? [X5] : (r1_tarski(X5,sK1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) => (r1_tarski(sK3(X4),sK1) & m1_connsp_2(sK3(X4),sK0,X4) & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(rectify,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f400,plain,(
% 0.20/0.53    ~spl5_38 | ~spl5_28 | ~spl5_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f396,f66,f270,f398])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    spl5_28 <=> r1_tarski(sK1,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    spl5_2 <=> ! [X3] : (~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.53  fof(f396,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK1) | ~m1_connsp_2(sK1,sK0,sK2) | ~spl5_2),
% 0.20/0.53    inference(resolution,[],[f67,f40])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2)) ) | ~spl5_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f66])).
% 0.20/0.53  fof(f356,plain,(
% 0.20/0.53    spl5_11 | spl5_9 | ~spl5_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f355,f63,f107,f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    spl5_11 <=> ! [X1,X2] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    spl5_1 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.53  fof(f355,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.53    inference(global_subsumption,[],[f39,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.20/0.53    inference(resolution,[],[f40,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.20/0.53  fof(f350,plain,(
% 0.20/0.53    spl5_8 | spl5_30),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f347])).
% 0.20/0.53  fof(f347,plain,(
% 0.20/0.53    $false | (spl5_8 | spl5_30)),
% 0.20/0.53    inference(subsumption_resolution,[],[f105,f336])).
% 0.20/0.53  fof(f336,plain,(
% 0.20/0.53    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl5_30),
% 0.20/0.53    inference(resolution,[],[f333,f57])).
% 0.20/0.53  % (6023)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f333,plain,(
% 0.20/0.53    ~r2_hidden(sK4(sK1,k1_tops_1(sK0,sK1)),sK1) | spl5_30),
% 0.20/0.53    inference(avatar_component_clause,[],[f332])).
% 0.20/0.53  fof(f332,plain,(
% 0.20/0.53    spl5_30 <=> r2_hidden(sK4(sK1,k1_tops_1(sK0,sK1)),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.53  % (6036)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl5_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    spl5_8 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.53  fof(f334,plain,(
% 0.20/0.53    spl5_8 | ~spl5_30 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_23),
% 0.20/0.53    inference(avatar_split_clause,[],[f329,f183,f87,f83,f79,f332,f104])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    spl5_5 <=> ! [X4] : (r1_tarski(sK3(X4),sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    spl5_6 <=> ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl5_7 <=> ! [X4] : (m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    spl5_23 <=> ! [X7,X6] : (~r2_hidden(X6,sK1) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,k1_tops_1(sK0,sK3(X6))) | ~m1_connsp_2(sK3(X6),sK0,X7))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.53  fof(f329,plain,(
% 0.20/0.53    ~r2_hidden(sK4(sK1,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_23)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f316])).
% 0.20/0.53  fof(f316,plain,(
% 0.20/0.53    ~r2_hidden(sK4(sK1,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_23)),
% 0.20/0.53    inference(resolution,[],[f312,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f312,plain,(
% 0.20/0.53    ( ! [X2] : (r2_hidden(sK4(sK1,X2),k1_tops_1(sK0,sK1)) | ~r2_hidden(sK4(sK1,X2),sK1) | r1_tarski(sK1,X2)) ) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_23)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f311])).
% 0.20/0.53  fof(f311,plain,(
% 0.20/0.53    ( ! [X2] : (r1_tarski(sK1,X2) | ~r2_hidden(sK4(sK1,X2),sK1) | r2_hidden(sK4(sK1,X2),k1_tops_1(sK0,sK1)) | ~r2_hidden(sK4(sK1,X2),sK1)) ) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_23)),
% 0.20/0.53    inference(resolution,[],[f298,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X7] : (m1_subset_1(X7,u1_struct_0(sK0)) | ~r2_hidden(X7,sK1)) )),
% 0.20/0.53    inference(resolution,[],[f40,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.53  fof(f298,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0) | ~r2_hidden(sK4(sK1,X0),sK1) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK1))) ) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_23)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f297])).
% 0.20/0.53  fof(f297,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(sK1,X0) | ~m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK1,X0),sK1) | r2_hidden(sK4(sK1,X0),k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))) ) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_23)),
% 0.20/0.53    inference(resolution,[],[f292,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X4] : (~m1_connsp_2(sK1,sK0,X4) | r2_hidden(X4,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 0.20/0.53    inference(global_subsumption,[],[f37,f38,f39,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X4] : (~m1_connsp_2(sK1,sK0,X4) | r2_hidden(X4,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f40,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    ( ! [X2] : (m1_connsp_2(sK1,sK0,sK4(sK1,X2)) | r1_tarski(sK1,X2) | ~m1_subset_1(sK4(sK1,X2),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK1,X2),sK1)) ) | (~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_23)),
% 0.20/0.53    inference(resolution,[],[f280,f230])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ( ! [X2] : (r2_hidden(X2,k1_tops_1(sK0,sK3(X2))) | ~r2_hidden(X2,sK1)) ) | (~spl5_6 | ~spl5_23)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f229])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    ( ! [X2] : (r2_hidden(X2,k1_tops_1(sK0,sK3(X2))) | ~r2_hidden(X2,sK1) | ~r2_hidden(X2,sK1)) ) | (~spl5_6 | ~spl5_23)),
% 0.20/0.53    inference(resolution,[],[f227,f96])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_tops_1(sK0,sK3(X0))) | ~r2_hidden(X0,sK1)) ) | (~spl5_6 | ~spl5_23)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f226])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_tops_1(sK0,sK3(X0))) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK1)) ) | (~spl5_6 | ~spl5_23)),
% 0.20/0.53    inference(resolution,[],[f184,f163])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ( ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~r2_hidden(X4,sK1)) ) | ~spl5_6),
% 0.20/0.53    inference(subsumption_resolution,[],[f84,f96])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1)) ) | ~spl5_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f83])).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    ( ! [X6,X7] : (~m1_connsp_2(sK3(X6),sK0,X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,k1_tops_1(sK0,sK3(X6))) | ~r2_hidden(X6,sK1)) ) | ~spl5_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f183])).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_tops_1(sK0,sK3(sK4(sK1,X0)))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tarski(sK1,X0) | m1_connsp_2(sK1,sK0,X1)) ) | (~spl5_5 | ~spl5_7)),
% 0.20/0.53    inference(resolution,[],[f265,f209])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~r1_tarski(X2,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | m1_connsp_2(sK1,sK0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f99,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl5_5 | ~spl5_7)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f263])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | (~spl5_5 | ~spl5_7)),
% 0.20/0.53    inference(resolution,[],[f240,f57])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK4(sK1,X0),sK1) | r1_tarski(k1_tops_1(sK0,sK3(sK4(sK1,X0))),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) ) | (~spl5_5 | ~spl5_7)),
% 0.20/0.53    inference(resolution,[],[f215,f165])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(sK3(sK4(sK1,X0)),sK1) | r1_tarski(sK1,X0)) ) | ~spl5_5),
% 0.20/0.53    inference(resolution,[],[f164,f57])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    ( ! [X4] : (~r2_hidden(X4,sK1) | r1_tarski(sK3(X4),sK1)) ) | ~spl5_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f80,f96])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | r1_tarski(sK3(X4),sK1) | ~r2_hidden(X4,sK1)) ) | ~spl5_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f79])).
% 0.20/0.53  fof(f215,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(sK3(X0),sK1) | r1_tarski(k1_tops_1(sK0,sK3(X0)),k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl5_7),
% 0.20/0.53    inference(resolution,[],[f100,f162])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    ( ! [X4] : (m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X4,sK1)) ) | ~spl5_7),
% 0.20/0.53    inference(subsumption_resolution,[],[f88,f96])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X4] : (m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1)) ) | ~spl5_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f87])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X6),k1_tops_1(sK0,sK1)) | ~r1_tarski(X6,sK1)) )),
% 0.20/0.53    inference(global_subsumption,[],[f39,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X6] : (~r1_tarski(X6,sK1) | r1_tarski(k1_tops_1(sK0,X6),k1_tops_1(sK0,sK1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f40,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.20/0.53  fof(f279,plain,(
% 0.20/0.53    spl5_28),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f276])).
% 0.20/0.53  fof(f276,plain,(
% 0.20/0.53    $false | spl5_28),
% 0.20/0.53    inference(resolution,[],[f271,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f271,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK1) | spl5_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f270])).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    ~spl5_9 | spl5_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f219,f63,f107])).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    v3_pre_topc(sK1,sK0) | sK1 != k1_tops_1(sK0,sK1)),
% 0.20/0.53    inference(global_subsumption,[],[f39,f38,f217])).
% 0.20/0.53  fof(f217,plain,(
% 0.20/0.53    v3_pre_topc(sK1,sK0) | sK1 != k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.53    inference(resolution,[],[f97,f40])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2) | k1_tops_1(X2,X3) != X3 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 0.20/0.53    inference(global_subsumption,[],[f39,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k1_tops_1(X2,X3) != X3 | v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 0.20/0.53    inference(resolution,[],[f40,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    ~spl5_10 | ~spl5_16 | ~spl5_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f198,f121,f138,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    spl5_10 <=> l1_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    spl5_16 <=> v2_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~spl5_11),
% 0.20/0.53    inference(resolution,[],[f122,f40])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2)) ) | ~spl5_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f121])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    spl5_15 | ~spl5_16 | ~spl5_10 | spl5_23 | ~spl5_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f169,f87,f183,f118,f138,f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl5_15 <=> v2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ( ! [X6,X7] : (~r2_hidden(X6,sK1) | ~m1_connsp_2(sK3(X6),sK0,X7) | r2_hidden(X7,k1_tops_1(sK0,sK3(X6))) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_7),
% 0.20/0.53    inference(resolution,[],[f162,f49])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    ~spl5_15),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f160])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    $false | ~spl5_15),
% 0.20/0.53    inference(subsumption_resolution,[],[f37,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    v2_struct_0(sK0) | ~spl5_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f135])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    spl5_16),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    $false | spl5_16),
% 0.20/0.53    inference(subsumption_resolution,[],[f38,f139])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ~v2_pre_topc(sK0) | spl5_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f138])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    spl5_10),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f156])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    $false | spl5_10),
% 0.20/0.53    inference(subsumption_resolution,[],[f39,f119])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | spl5_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f118])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ~spl5_8 | spl5_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f102,f107,f104])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f101,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.53    inference(global_subsumption,[],[f39,f95])).
% 0.20/0.53  % (6030)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(resolution,[],[f40,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl5_1 | spl5_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f41,f87,f63])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X4] : (m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    spl5_1 | spl5_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f42,f83,f63])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    spl5_1 | spl5_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f43,f79,f63])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X4] : (r1_tarski(sK3(X4),sK1) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ~spl5_1 | spl5_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f44,f74,f63])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ~spl5_1 | spl5_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f45,f70,f63])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ~spl5_1 | spl5_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f46,f66,f63])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (6011)------------------------------
% 0.20/0.53  % (6011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6011)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (6011)Memory used [KB]: 11001
% 0.20/0.53  % (6011)Time elapsed: 0.102 s
% 0.20/0.53  % (6011)------------------------------
% 0.20/0.53  % (6011)------------------------------
% 0.20/0.53  % (6030)Refutation not found, incomplete strategy% (6030)------------------------------
% 0.20/0.53  % (6030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6030)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6030)Memory used [KB]: 1791
% 0.20/0.53  % (6030)Time elapsed: 0.126 s
% 0.20/0.53  % (6030)------------------------------
% 0.20/0.53  % (6030)------------------------------
% 0.20/0.54  % (6007)Success in time 0.178 s
%------------------------------------------------------------------------------
