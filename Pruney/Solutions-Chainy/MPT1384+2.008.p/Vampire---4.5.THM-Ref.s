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

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  124 (3923 expanded)
%              Number of leaves         :   25 (1409 expanded)
%              Depth                    :   20
%              Number of atoms          :  668 (43950 expanded)
%              Number of equality atoms :   17 ( 431 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f702,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f111,f115,f119,f123,f588,f701])).

fof(f701,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f700])).

fof(f700,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f699,f692])).

fof(f692,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f105,f96,f55,f110,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f110,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl10_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,(
    ! [X4] :
      ( ? [X5] :
          ( r1_tarski(X5,sK1)
          & m1_connsp_2(X5,sK0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
     => ( r1_tarski(sK3(X4),sK1)
        & m1_connsp_2(sK3(X4),sK0,X4)
        & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f96,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl10_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f105,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f699,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK2)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f85,f55,f100])).

fof(f100,plain,
    ( ! [X3] :
        ( ~ m1_connsp_2(X3,sK0,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl10_2
  <=> ! [X3] :
        ( ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f588,plain,
    ( spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f580,f572])).

fof(f572,plain,
    ( ~ r1_tarski(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1)
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f258,f191,f353,f352,f355,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK4(X0,X1,X2))
                    & r1_tarski(sK4(X0,X1,X2),X2)
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK4(X0,X1,X2))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f355,plain,
    ( r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))))
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f191,f255,f256,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK4(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f256,plain,
    ( m1_connsp_2(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
    | spl10_1
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f167,f191,f118])).

fof(f118,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X4),sK0,X4) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl10_6
  <=> ! [X4] :
        ( m1_connsp_2(sK3(X4),sK0,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f167,plain,
    ( r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f153,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f153,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f124,f142,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f142,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f97,f55,f128,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f86_D])).

fof(f86_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( v3_pre_topc(X2,X0)
          | k1_tops_1(X0,X2) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f128,plain,(
    ~ sP6(sK0) ),
    inference(unit_resulting_resolution,[],[f54,f53,f125,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0)
      | sP7 ) ),
    inference(cnf_transformation,[],[f88_D])).

fof(f88_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP6(X0) )
  <=> ~ sP7 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f125,plain,(
    ~ sP7 ),
    inference(unit_resulting_resolution,[],[f54,f55,f89])).

fof(f89,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP7 ) ),
    inference(general_splitting,[],[f87,f88_D])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f72,f86_D])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f97,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f124,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f54,f55,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f255,plain,
    ( m1_subset_1(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_1
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f167,f191,f122])).

fof(f122,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl10_7
  <=> ! [X4] :
        ( m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f352,plain,
    ( m1_subset_1(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f191,f255,f256,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f353,plain,
    ( v3_pre_topc(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK0)
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f191,f255,f256,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f191,plain,
    ( m1_subset_1(sK5(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f55,f167,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f258,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f168,f191,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f168,plain,
    ( ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f153,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f580,plain,
    ( r1_tarski(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1)
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f257,f354,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f354,plain,
    ( r1_tarski(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK3(sK5(sK1,k1_tops_1(sK0,sK1))))
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f191,f255,f256,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f257,plain,
    ( r1_tarski(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),sK1)
    | spl10_1
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f167,f191,f114])).

fof(f114,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_tarski(sK3(X4),sK1) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl10_5
  <=> ! [X4] :
        ( r1_tarski(sK3(X4),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f123,plain,
    ( spl10_1
    | spl10_7 ),
    inference(avatar_split_clause,[],[f56,f121,f95])).

fof(f56,plain,(
    ! [X4] :
      ( m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f119,plain,
    ( spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f57,f117,f95])).

fof(f57,plain,(
    ! [X4] :
      ( m1_connsp_2(sK3(X4),sK0,X4)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,
    ( spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f58,f113,f95])).

fof(f58,plain,(
    ! [X4] :
      ( r1_tarski(sK3(X4),sK1)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f111,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f59,f108,f95])).

fof(f59,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f60,f103,f95])).

fof(f60,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f61,f99,f95])).

fof(f61,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:29:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (18794)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (18800)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (18815)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (18792)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (18793)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (18790)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (18802)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (18803)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (18795)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (18798)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (18804)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (18809)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (18812)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (18807)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (18796)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (18813)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.53  % (18811)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.53  % (18801)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.53  % (18791)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (18789)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.54  % (18814)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.54  % (18818)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.54  % (18816)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.54  % (18806)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.55  % (18810)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (18808)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (18799)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (18797)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (18805)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (18815)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.56  % (18817)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.57  % SZS output start Proof for theBenchmark
% 1.41/0.57  fof(f702,plain,(
% 1.41/0.57    $false),
% 1.41/0.57    inference(avatar_sat_refutation,[],[f101,f106,f111,f115,f119,f123,f588,f701])).
% 1.41/0.57  fof(f701,plain,(
% 1.41/0.57    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f700])).
% 1.41/0.57  fof(f700,plain,(
% 1.41/0.57    $false | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4)),
% 1.41/0.57    inference(subsumption_resolution,[],[f699,f692])).
% 1.41/0.57  fof(f692,plain,(
% 1.41/0.57    m1_connsp_2(sK1,sK0,sK2) | (~spl10_1 | ~spl10_3 | ~spl10_4)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f52,f53,f54,f105,f96,f55,f110,f70])).
% 1.41/0.57  fof(f70,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f22])).
% 1.41/0.57  fof(f22,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.57    inference(flattening,[],[f21])).
% 1.41/0.57  fof(f21,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f10])).
% 1.41/0.57  fof(f10,axiom,(
% 1.41/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.41/0.57  fof(f110,plain,(
% 1.41/0.57    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl10_4),
% 1.41/0.57    inference(avatar_component_clause,[],[f108])).
% 1.41/0.57  fof(f108,plain,(
% 1.41/0.57    spl10_4 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.41/0.57  fof(f55,plain,(
% 1.41/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.57    inference(cnf_transformation,[],[f39])).
% 1.41/0.57  fof(f39,plain,(
% 1.41/0.57    (((! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & (! [X4] : ((r1_tarski(sK3(X4),sK1) & m1_connsp_2(sK3(X4),sK0,X4) & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.41/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37,f36,f35])).
% 1.41/0.57  fof(f35,plain,(
% 1.41/0.57    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.41/0.57    introduced(choice_axiom,[])).
% 1.41/0.57  fof(f36,plain,(
% 1.41/0.57    ? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.41/0.57    introduced(choice_axiom,[])).
% 1.41/0.57  fof(f37,plain,(
% 1.41/0.57    ? [X2] : (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.41/0.57    introduced(choice_axiom,[])).
% 1.41/0.57  fof(f38,plain,(
% 1.41/0.57    ! [X4] : (? [X5] : (r1_tarski(X5,sK1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) => (r1_tarski(sK3(X4),sK1) & m1_connsp_2(sK3(X4),sK0,X4) & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.41/0.57    introduced(choice_axiom,[])).
% 1.41/0.57  fof(f34,plain,(
% 1.41/0.57    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.41/0.57    inference(rectify,[],[f33])).
% 1.41/0.57  fof(f33,plain,(
% 1.41/0.57    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.41/0.57    inference(flattening,[],[f32])).
% 1.41/0.57  fof(f32,plain,(
% 1.41/0.57    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.41/0.57    inference(nnf_transformation,[],[f15])).
% 1.41/0.57  fof(f15,plain,(
% 1.41/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.41/0.57    inference(flattening,[],[f14])).
% 1.41/0.57  fof(f14,plain,(
% 1.41/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f13])).
% 1.41/0.57  fof(f13,negated_conjecture,(
% 1.41/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.41/0.57    inference(negated_conjecture,[],[f12])).
% 1.41/0.57  fof(f12,conjecture,(
% 1.41/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 1.41/0.57  fof(f96,plain,(
% 1.41/0.57    v3_pre_topc(sK1,sK0) | ~spl10_1),
% 1.41/0.57    inference(avatar_component_clause,[],[f95])).
% 1.41/0.57  fof(f95,plain,(
% 1.41/0.57    spl10_1 <=> v3_pre_topc(sK1,sK0)),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.41/0.57  fof(f105,plain,(
% 1.41/0.57    r2_hidden(sK2,sK1) | ~spl10_3),
% 1.41/0.57    inference(avatar_component_clause,[],[f103])).
% 1.41/0.57  fof(f103,plain,(
% 1.41/0.57    spl10_3 <=> r2_hidden(sK2,sK1)),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.41/0.57  fof(f54,plain,(
% 1.41/0.57    l1_pre_topc(sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f39])).
% 1.41/0.57  fof(f53,plain,(
% 1.41/0.57    v2_pre_topc(sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f39])).
% 1.41/0.57  fof(f52,plain,(
% 1.41/0.57    ~v2_struct_0(sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f39])).
% 1.41/0.57  fof(f699,plain,(
% 1.41/0.57    ~m1_connsp_2(sK1,sK0,sK2) | ~spl10_2),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f85,f55,f100])).
% 1.41/0.57  fof(f100,plain,(
% 1.41/0.57    ( ! [X3] : (~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1)) ) | ~spl10_2),
% 1.41/0.57    inference(avatar_component_clause,[],[f99])).
% 1.41/0.57  fof(f99,plain,(
% 1.41/0.57    spl10_2 <=> ! [X3] : (~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2))),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.41/0.57  fof(f85,plain,(
% 1.41/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.57    inference(equality_resolution,[],[f74])).
% 1.41/0.57  fof(f74,plain,(
% 1.41/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.41/0.57    inference(cnf_transformation,[],[f46])).
% 1.41/0.57  fof(f46,plain,(
% 1.41/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.57    inference(flattening,[],[f45])).
% 1.41/0.57  fof(f45,plain,(
% 1.41/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.57    inference(nnf_transformation,[],[f2])).
% 1.41/0.57  fof(f2,axiom,(
% 1.41/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.57  fof(f588,plain,(
% 1.41/0.57    spl10_1 | ~spl10_5 | ~spl10_6 | ~spl10_7),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f587])).
% 1.41/0.57  fof(f587,plain,(
% 1.41/0.57    $false | (spl10_1 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 1.41/0.57    inference(subsumption_resolution,[],[f580,f572])).
% 1.41/0.57  fof(f572,plain,(
% 1.41/0.57    ~r1_tarski(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.41/0.57    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f258,f191,f353,f352,f355,f69])).
% 1.41/0.57  fof(f69,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f44])).
% 1.41/0.57  fof(f44,plain,(
% 1.41/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK4(X0,X1,X2)) & r1_tarski(sK4(X0,X1,X2),X2) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 1.41/0.57  fof(f43,plain,(
% 1.41/0.57    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4(X0,X1,X2)) & r1_tarski(sK4(X0,X1,X2),X2) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.41/0.57    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f42,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.58    inference(rectify,[],[f41])).
% 1.41/0.58  fof(f41,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.58    inference(nnf_transformation,[],[f20])).
% 1.41/0.58  fof(f20,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.58    inference(flattening,[],[f19])).
% 1.41/0.58  fof(f19,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.41/0.58    inference(ennf_transformation,[],[f11])).
% 1.41/0.58  fof(f11,axiom,(
% 1.41/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 1.41/0.58  fof(f355,plain,(
% 1.41/0.58    r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1))))) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f52,f53,f54,f191,f255,f256,f68])).
% 1.41/0.58  fof(f68,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (r2_hidden(X1,sK4(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f44])).
% 1.41/0.58  fof(f256,plain,(
% 1.41/0.58    m1_connsp_2(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),sK0,sK5(sK1,k1_tops_1(sK0,sK1))) | (spl10_1 | ~spl10_6)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f167,f191,f118])).
% 1.41/0.58  fof(f118,plain,(
% 1.41/0.58    ( ! [X4] : (~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m1_connsp_2(sK3(X4),sK0,X4)) ) | ~spl10_6),
% 1.41/0.58    inference(avatar_component_clause,[],[f117])).
% 1.41/0.58  fof(f117,plain,(
% 1.41/0.58    spl10_6 <=> ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.41/0.58  fof(f167,plain,(
% 1.41/0.58    r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1) | spl10_1),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f153,f78])).
% 1.41/0.58  fof(f78,plain,(
% 1.41/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f50])).
% 1.41/0.58  fof(f50,plain,(
% 1.41/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).
% 1.41/0.58  fof(f49,plain,(
% 1.41/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.41/0.58    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f48,plain,(
% 1.41/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.58    inference(rectify,[],[f47])).
% 1.41/0.58  fof(f47,plain,(
% 1.41/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.58    inference(nnf_transformation,[],[f27])).
% 1.41/0.58  fof(f27,plain,(
% 1.41/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.58    inference(ennf_transformation,[],[f1])).
% 1.41/0.58  fof(f1,axiom,(
% 1.41/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.58  fof(f153,plain,(
% 1.41/0.58    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl10_1),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f124,f142,f76])).
% 1.41/0.58  fof(f76,plain,(
% 1.41/0.58    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f46])).
% 1.41/0.58  fof(f142,plain,(
% 1.41/0.58    sK1 != k1_tops_1(sK0,sK1) | spl10_1),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f97,f55,f128,f86])).
% 1.41/0.58  fof(f86,plain,(
% 1.41/0.58    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP6(X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f86_D])).
% 1.41/0.58  fof(f86_D,plain,(
% 1.41/0.58    ( ! [X0] : (( ! [X2] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) <=> ~sP6(X0)) )),
% 1.41/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.41/0.58  fof(f128,plain,(
% 1.41/0.58    ~sP6(sK0)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f54,f53,f125,f88])).
% 1.41/0.58  fof(f88,plain,(
% 1.41/0.58    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0) | sP7) )),
% 1.41/0.58    inference(cnf_transformation,[],[f88_D])).
% 1.41/0.58  fof(f88_D,plain,(
% 1.41/0.58    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) ) <=> ~sP7),
% 1.41/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.41/0.58  fof(f125,plain,(
% 1.41/0.58    ~sP7),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f54,f55,f89])).
% 1.41/0.58  fof(f89,plain,(
% 1.41/0.58    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP7) )),
% 1.41/0.58    inference(general_splitting,[],[f87,f88_D])).
% 1.41/0.58  fof(f87,plain,(
% 1.41/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) )),
% 1.41/0.58    inference(general_splitting,[],[f72,f86_D])).
% 1.41/0.58  fof(f72,plain,(
% 1.41/0.58    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f24])).
% 1.41/0.58  fof(f24,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.41/0.58    inference(flattening,[],[f23])).
% 1.41/0.58  fof(f23,plain,(
% 1.41/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.41/0.58    inference(ennf_transformation,[],[f7])).
% 1.41/0.58  fof(f7,axiom,(
% 1.41/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 1.41/0.58  fof(f97,plain,(
% 1.41/0.58    ~v3_pre_topc(sK1,sK0) | spl10_1),
% 1.41/0.58    inference(avatar_component_clause,[],[f95])).
% 1.41/0.58  fof(f124,plain,(
% 1.41/0.58    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f54,f55,f62])).
% 1.41/0.59  fof(f62,plain,(
% 1.41/0.59    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f16])).
% 1.41/0.59  fof(f16,plain,(
% 1.41/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.59    inference(ennf_transformation,[],[f6])).
% 1.41/0.59  fof(f6,axiom,(
% 1.41/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.41/0.59  fof(f255,plain,(
% 1.41/0.59    m1_subset_1(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl10_1 | ~spl10_7)),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f167,f191,f122])).
% 1.41/0.59  fof(f122,plain,(
% 1.41/0.59    ( ! [X4] : (~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl10_7),
% 1.41/0.59    inference(avatar_component_clause,[],[f121])).
% 1.41/0.59  fof(f121,plain,(
% 1.41/0.59    spl10_7 <=> ! [X4] : (m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 1.41/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.41/0.59  fof(f352,plain,(
% 1.41/0.59    m1_subset_1(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f52,f53,f54,f191,f255,f256,f65])).
% 1.41/0.59  fof(f65,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f44])).
% 1.41/0.59  fof(f353,plain,(
% 1.41/0.59    v3_pre_topc(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK0) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f52,f53,f54,f191,f255,f256,f66])).
% 1.41/0.59  fof(f66,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f44])).
% 1.41/0.59  fof(f191,plain,(
% 1.41/0.59    m1_subset_1(sK5(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | spl10_1),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f55,f167,f82])).
% 1.41/0.59  fof(f82,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f29])).
% 1.41/0.59  fof(f29,plain,(
% 1.41/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.41/0.59    inference(flattening,[],[f28])).
% 1.41/0.59  fof(f28,plain,(
% 1.41/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.41/0.59    inference(ennf_transformation,[],[f5])).
% 1.41/0.59  fof(f5,axiom,(
% 1.41/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.41/0.59  fof(f258,plain,(
% 1.41/0.59    ~m1_connsp_2(sK1,sK0,sK5(sK1,k1_tops_1(sK0,sK1))) | spl10_1),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f52,f53,f54,f55,f168,f191,f63])).
% 1.41/0.59  fof(f63,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f40])).
% 1.41/0.59  fof(f40,plain,(
% 1.41/0.59    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.59    inference(nnf_transformation,[],[f18])).
% 1.41/0.59  fof(f18,plain,(
% 1.41/0.59    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.41/0.59    inference(flattening,[],[f17])).
% 1.41/0.59  fof(f17,plain,(
% 1.41/0.59    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.41/0.59    inference(ennf_transformation,[],[f8])).
% 1.41/0.59  fof(f8,axiom,(
% 1.41/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.41/0.59  fof(f168,plain,(
% 1.41/0.59    ~r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | spl10_1),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f153,f79])).
% 1.41/0.59  fof(f79,plain,(
% 1.41/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f50])).
% 1.41/0.59  fof(f580,plain,(
% 1.41/0.59    r1_tarski(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1) | (spl10_1 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f257,f354,f83])).
% 1.41/0.59  fof(f83,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f31])).
% 1.41/0.59  fof(f31,plain,(
% 1.41/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.41/0.59    inference(flattening,[],[f30])).
% 1.41/0.59  fof(f30,plain,(
% 1.41/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.41/0.59    inference(ennf_transformation,[],[f3])).
% 1.41/0.59  fof(f3,axiom,(
% 1.41/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.41/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.41/0.59  fof(f354,plain,(
% 1.41/0.59    r1_tarski(sK4(sK0,sK5(sK1,k1_tops_1(sK0,sK1)),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f52,f53,f54,f191,f255,f256,f67])).
% 1.41/0.59  fof(f67,plain,(
% 1.41/0.59    ( ! [X2,X0,X1] : (r1_tarski(sK4(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f44])).
% 1.41/0.59  fof(f257,plain,(
% 1.41/0.59    r1_tarski(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),sK1) | (spl10_1 | ~spl10_5)),
% 1.41/0.59    inference(unit_resulting_resolution,[],[f167,f191,f114])).
% 1.41/0.59  fof(f114,plain,(
% 1.41/0.59    ( ! [X4] : (~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_tarski(sK3(X4),sK1)) ) | ~spl10_5),
% 1.41/0.59    inference(avatar_component_clause,[],[f113])).
% 1.41/0.59  fof(f113,plain,(
% 1.41/0.59    spl10_5 <=> ! [X4] : (r1_tarski(sK3(X4),sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 1.41/0.59    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.41/0.59  fof(f123,plain,(
% 1.41/0.59    spl10_1 | spl10_7),
% 1.41/0.59    inference(avatar_split_clause,[],[f56,f121,f95])).
% 1.41/0.59  fof(f56,plain,(
% 1.41/0.59    ( ! [X4] : (m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f39])).
% 1.41/0.59  fof(f119,plain,(
% 1.41/0.59    spl10_1 | spl10_6),
% 1.41/0.59    inference(avatar_split_clause,[],[f57,f117,f95])).
% 1.41/0.59  fof(f57,plain,(
% 1.41/0.59    ( ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f39])).
% 1.41/0.59  fof(f115,plain,(
% 1.41/0.59    spl10_1 | spl10_5),
% 1.41/0.59    inference(avatar_split_clause,[],[f58,f113,f95])).
% 1.41/0.59  fof(f58,plain,(
% 1.41/0.59    ( ! [X4] : (r1_tarski(sK3(X4),sK1) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f39])).
% 1.41/0.59  fof(f111,plain,(
% 1.41/0.59    ~spl10_1 | spl10_4),
% 1.41/0.59    inference(avatar_split_clause,[],[f59,f108,f95])).
% 1.41/0.59  fof(f59,plain,(
% 1.41/0.59    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.41/0.59    inference(cnf_transformation,[],[f39])).
% 1.41/0.59  fof(f106,plain,(
% 1.41/0.59    ~spl10_1 | spl10_3),
% 1.41/0.59    inference(avatar_split_clause,[],[f60,f103,f95])).
% 1.41/0.59  fof(f60,plain,(
% 1.41/0.59    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.41/0.59    inference(cnf_transformation,[],[f39])).
% 1.41/0.59  fof(f101,plain,(
% 1.41/0.59    ~spl10_1 | spl10_2),
% 1.41/0.59    inference(avatar_split_clause,[],[f61,f99,f95])).
% 1.41/0.59  fof(f61,plain,(
% 1.41/0.59    ( ! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) )),
% 1.41/0.59    inference(cnf_transformation,[],[f39])).
% 1.41/0.59  % SZS output end Proof for theBenchmark
% 1.41/0.59  % (18815)------------------------------
% 1.41/0.59  % (18815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.59  % (18815)Termination reason: Refutation
% 1.41/0.59  
% 1.41/0.59  % (18815)Memory used [KB]: 11001
% 1.41/0.59  % (18815)Time elapsed: 0.139 s
% 1.41/0.59  % (18815)------------------------------
% 1.41/0.59  % (18815)------------------------------
% 1.41/0.59  % (18788)Success in time 0.234 s
%------------------------------------------------------------------------------
