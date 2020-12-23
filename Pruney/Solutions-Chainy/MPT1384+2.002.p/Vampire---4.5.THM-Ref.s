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
% DateTime   : Thu Dec  3 13:15:06 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  128 (4478 expanded)
%              Number of leaves         :   26 (1605 expanded)
%              Depth                    :   22
%              Number of atoms          :  668 (49976 expanded)
%              Number of equality atoms :   17 ( 482 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f516,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f119,f123,f127,f466,f515])).

fof(f515,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f513,f512])).

fof(f512,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f109,f100,f58,f114,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f114,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl10_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,(
    ! [X4] :
      ( ? [X5] :
          ( r1_tarski(X5,sK1)
          & m1_connsp_2(X5,sK0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
     => ( r1_tarski(sK3(X4),sK1)
        & m1_connsp_2(sK3(X4),sK0,X4)
        & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f100,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl10_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f109,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl10_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f513,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK2)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f89,f58,f104])).

fof(f104,plain,
    ( ! [X3] :
        ( ~ m1_connsp_2(X3,sK0,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_2
  <=> ! [X3] :
        ( ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f466,plain,
    ( spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f458,f425])).

fof(f425,plain,
    ( ~ r2_hidden(sK5(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1),sK3(sK5(sK1,k1_tops_1(sK0,sK1))))
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f196,f321,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f321,plain,
    ( ~ r2_hidden(sK5(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1),sK1)
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f267,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f267,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1)
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f58,f197,f184,f221,f222,f232,f72])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
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

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f232,plain,
    ( r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))))
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f184,f194,f195,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f195,plain,
    ( m1_connsp_2(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
    | spl10_1
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f162,f184,f122])).

fof(f122,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X4),sK0,X4) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl10_6
  <=> ! [X4] :
        ( m1_connsp_2(sK3(X4),sK0,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f162,plain,
    ( r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f158,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f158,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f128,f151,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f151,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f101,f58,f134,f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f90_D])).

fof(f90_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( v3_pre_topc(X2,X0)
          | k1_tops_1(X0,X2) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f134,plain,(
    ~ sP6(sK0) ),
    inference(unit_resulting_resolution,[],[f57,f56,f131,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0)
      | sP7 ) ),
    inference(cnf_transformation,[],[f92_D])).

fof(f92_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP6(X0) )
  <=> ~ sP7 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f131,plain,(
    ~ sP7 ),
    inference(unit_resulting_resolution,[],[f57,f58,f93])).

fof(f93,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP7 ) ),
    inference(general_splitting,[],[f91,f92_D])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f75,f90_D])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f101,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f128,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f57,f58,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f194,plain,
    ( m1_subset_1(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_1
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f162,f184,f126])).

fof(f126,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl10_7
  <=> ! [X4] :
        ( m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f222,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_1
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f57,f194,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f221,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK0)
    | spl10_1
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f56,f57,f194,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f184,plain,
    ( m1_subset_1(sK5(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f58,f162,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f197,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f58,f163,f184,f66])).

fof(f163,plain,
    ( ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f158,f84])).

fof(f196,plain,
    ( r1_tarski(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),sK1)
    | spl10_1
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f162,f184,f118])).

fof(f118,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_tarski(sK3(X4),sK1) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl10_5
  <=> ! [X4] :
        ( r1_tarski(sK3(X4),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f458,plain,
    ( r2_hidden(sK5(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1),sK3(sK5(sK1,k1_tops_1(sK0,sK1))))
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f220,f320,f82])).

fof(f320,plain,
    ( r2_hidden(sK5(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1),k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))))
    | spl10_1
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f267,f83])).

fof(f220,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK3(sK5(sK1,k1_tops_1(sK0,sK1))))
    | spl10_1
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f57,f194,f65])).

fof(f127,plain,
    ( spl10_1
    | spl10_7 ),
    inference(avatar_split_clause,[],[f59,f125,f99])).

fof(f59,plain,(
    ! [X4] :
      ( m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,
    ( spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f60,f121,f99])).

fof(f60,plain,(
    ! [X4] :
      ( m1_connsp_2(sK3(X4),sK0,X4)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,
    ( spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f61,f117,f99])).

fof(f61,plain,(
    ! [X4] :
      ( r1_tarski(sK3(X4),sK1)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f115,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f62,f112,f99])).

fof(f62,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f110,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f63,f107,f99])).

fof(f63,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f64,f103,f99])).

fof(f64,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:10:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (29114)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (29117)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (29118)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (29115)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (29122)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (29138)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (29126)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (29127)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (29131)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (29137)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (29129)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (29124)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (29134)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (29119)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.54  % (29121)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (29133)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.54  % (29139)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.54  % (29140)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.54  % (29120)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.54  % (29130)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.55  % (29141)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.55  % (29132)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  % (29142)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.55  % (29125)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (29123)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.55  % (29135)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.57  % (29136)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.57  % (29116)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.52/0.57  % (29143)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.57  % (29140)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f516,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f105,f110,f115,f119,f123,f127,f466,f515])).
% 1.52/0.57  fof(f515,plain,(
% 1.52/0.57    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f514])).
% 1.52/0.57  fof(f514,plain,(
% 1.52/0.57    $false | (~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4)),
% 1.52/0.57    inference(subsumption_resolution,[],[f513,f512])).
% 1.52/0.57  fof(f512,plain,(
% 1.52/0.57    m1_connsp_2(sK1,sK0,sK2) | (~spl10_1 | ~spl10_3 | ~spl10_4)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f55,f56,f57,f109,f100,f58,f114,f73])).
% 1.52/0.57  fof(f73,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f22])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f11])).
% 1.52/0.57  fof(f11,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.52/0.57  fof(f114,plain,(
% 1.52/0.57    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl10_4),
% 1.52/0.57    inference(avatar_component_clause,[],[f112])).
% 1.52/0.57  fof(f112,plain,(
% 1.52/0.57    spl10_4 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.52/0.57  fof(f58,plain,(
% 1.52/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    (((! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & (! [X4] : ((r1_tarski(sK3(X4),sK1) & m1_connsp_2(sK3(X4),sK0,X4) & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40,f39,f38])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ? [X2] : (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ! [X4] : (? [X5] : (r1_tarski(X5,sK1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) => (r1_tarski(sK3(X4),sK1) & m1_connsp_2(sK3(X4),sK0,X4) & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.57    inference(rectify,[],[f36])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f35])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.57    inference(nnf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f15])).
% 1.52/0.57  fof(f15,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,negated_conjecture,(
% 1.52/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.52/0.57    inference(negated_conjecture,[],[f13])).
% 1.52/0.57  fof(f13,conjecture,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 1.52/0.57  fof(f100,plain,(
% 1.52/0.57    v3_pre_topc(sK1,sK0) | ~spl10_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f99])).
% 1.52/0.57  fof(f99,plain,(
% 1.52/0.57    spl10_1 <=> v3_pre_topc(sK1,sK0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.52/0.57  fof(f109,plain,(
% 1.52/0.57    r2_hidden(sK2,sK1) | ~spl10_3),
% 1.52/0.57    inference(avatar_component_clause,[],[f107])).
% 1.52/0.57  fof(f107,plain,(
% 1.52/0.57    spl10_3 <=> r2_hidden(sK2,sK1)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.52/0.57  fof(f57,plain,(
% 1.52/0.57    l1_pre_topc(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f56,plain,(
% 1.52/0.57    v2_pre_topc(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    ~v2_struct_0(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f513,plain,(
% 1.52/0.57    ~m1_connsp_2(sK1,sK0,sK2) | ~spl10_2),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f89,f58,f104])).
% 1.52/0.57  fof(f104,plain,(
% 1.52/0.57    ( ! [X3] : (~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1)) ) | ~spl10_2),
% 1.52/0.57    inference(avatar_component_clause,[],[f103])).
% 1.52/0.57  fof(f103,plain,(
% 1.52/0.57    spl10_2 <=> ! [X3] : (~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.52/0.57  fof(f89,plain,(
% 1.52/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.57    inference(equality_resolution,[],[f79])).
% 1.52/0.57  fof(f79,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f49])).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.57    inference(flattening,[],[f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.57    inference(nnf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.57  fof(f466,plain,(
% 1.52/0.57    spl10_1 | ~spl10_5 | ~spl10_6 | ~spl10_7),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f465])).
% 1.52/0.57  fof(f465,plain,(
% 1.52/0.57    $false | (spl10_1 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 1.52/0.57    inference(subsumption_resolution,[],[f458,f425])).
% 1.52/0.57  fof(f425,plain,(
% 1.52/0.57    ~r2_hidden(sK5(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))) | (spl10_1 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f196,f321,f82])).
% 1.52/0.57  fof(f82,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f53])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).
% 1.52/0.57  fof(f52,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(rectify,[],[f50])).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(nnf_transformation,[],[f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.57  fof(f321,plain,(
% 1.52/0.57    ~r2_hidden(sK5(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1),sK1) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f267,f84])).
% 1.52/0.57  fof(f84,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f53])).
% 1.52/0.57  fof(f267,plain,(
% 1.52/0.57    ~r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f55,f56,f57,f58,f197,f184,f221,f222,f232,f72])).
% 1.52/0.57  fof(f72,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK4(X0,X1,X2)) & r1_tarski(sK4(X0,X1,X2),X2) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK4(X0,X1,X2)) & r1_tarski(sK4(X0,X1,X2),X2) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(rectify,[],[f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(nnf_transformation,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).
% 1.52/0.57  fof(f232,plain,(
% 1.52/0.57    r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1))))) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f55,f56,f57,f184,f194,f195,f66])).
% 1.52/0.57  fof(f66,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f43])).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(nnf_transformation,[],[f19])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f18])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.52/0.57  fof(f195,plain,(
% 1.52/0.57    m1_connsp_2(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),sK0,sK5(sK1,k1_tops_1(sK0,sK1))) | (spl10_1 | ~spl10_6)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f162,f184,f122])).
% 1.52/0.57  fof(f122,plain,(
% 1.52/0.57    ( ! [X4] : (~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m1_connsp_2(sK3(X4),sK0,X4)) ) | ~spl10_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f121])).
% 1.52/0.57  fof(f121,plain,(
% 1.52/0.57    spl10_6 <=> ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.52/0.57  fof(f162,plain,(
% 1.52/0.57    r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),sK1) | spl10_1),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f158,f83])).
% 1.52/0.57  fof(f83,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f53])).
% 1.52/0.57  fof(f158,plain,(
% 1.52/0.57    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl10_1),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f128,f151,f81])).
% 1.52/0.57  fof(f81,plain,(
% 1.52/0.57    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f49])).
% 1.52/0.57  fof(f151,plain,(
% 1.52/0.57    sK1 != k1_tops_1(sK0,sK1) | spl10_1),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f101,f58,f134,f90])).
% 1.52/0.57  fof(f90,plain,(
% 1.52/0.57    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP6(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f90_D])).
% 1.52/0.57  fof(f90_D,plain,(
% 1.52/0.57    ( ! [X0] : (( ! [X2] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) <=> ~sP6(X0)) )),
% 1.52/0.57    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.52/0.57  fof(f134,plain,(
% 1.52/0.57    ~sP6(sK0)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f57,f56,f131,f92])).
% 1.52/0.57  fof(f92,plain,(
% 1.52/0.57    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0) | sP7) )),
% 1.52/0.57    inference(cnf_transformation,[],[f92_D])).
% 1.52/0.57  fof(f92_D,plain,(
% 1.52/0.57    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) ) <=> ~sP7),
% 1.52/0.57    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.52/0.57  fof(f131,plain,(
% 1.52/0.57    ~sP7),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f57,f58,f93])).
% 1.52/0.57  fof(f93,plain,(
% 1.52/0.57    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP7) )),
% 1.52/0.57    inference(general_splitting,[],[f91,f92_D])).
% 1.52/0.57  fof(f91,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) )),
% 1.52/0.57    inference(general_splitting,[],[f75,f90_D])).
% 1.52/0.57  fof(f75,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.52/0.57    inference(flattening,[],[f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 1.52/0.57  fof(f101,plain,(
% 1.52/0.57    ~v3_pre_topc(sK1,sK0) | spl10_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f99])).
% 1.52/0.57  fof(f128,plain,(
% 1.52/0.57    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f57,f58,f65])).
% 1.52/0.57  fof(f65,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,axiom,(
% 1.52/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.52/0.57  fof(f194,plain,(
% 1.52/0.57    m1_subset_1(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl10_1 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f162,f184,f126])).
% 1.52/0.57  fof(f126,plain,(
% 1.52/0.57    ( ! [X4] : (~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl10_7),
% 1.52/0.57    inference(avatar_component_clause,[],[f125])).
% 1.52/0.57  fof(f125,plain,(
% 1.52/0.57    spl10_7 <=> ! [X4] : (m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.52/0.57  fof(f222,plain,(
% 1.52/0.57    m1_subset_1(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl10_1 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f57,f194,f78])).
% 1.52/0.57  fof(f78,plain,(
% 1.52/0.57    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f31])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.52/0.57    inference(flattening,[],[f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.52/0.57  fof(f221,plain,(
% 1.52/0.57    v3_pre_topc(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK0) | (spl10_1 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f56,f57,f194,f77])).
% 1.52/0.57  fof(f77,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.52/0.57    inference(flattening,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.52/0.57  fof(f184,plain,(
% 1.52/0.57    m1_subset_1(sK5(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | spl10_1),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f58,f162,f87])).
% 1.52/0.57  fof(f87,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f34])).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.52/0.57    inference(flattening,[],[f33])).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.52/0.57    inference(ennf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.52/0.57  fof(f197,plain,(
% 1.52/0.57    ~m1_connsp_2(sK1,sK0,sK5(sK1,k1_tops_1(sK0,sK1))) | spl10_1),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f55,f56,f57,f58,f163,f184,f66])).
% 1.52/0.57  fof(f163,plain,(
% 1.52/0.57    ~r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | spl10_1),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f158,f84])).
% 1.52/0.57  fof(f196,plain,(
% 1.52/0.57    r1_tarski(sK3(sK5(sK1,k1_tops_1(sK0,sK1))),sK1) | (spl10_1 | ~spl10_5)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f162,f184,f118])).
% 1.52/0.57  fof(f118,plain,(
% 1.52/0.57    ( ! [X4] : (~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_tarski(sK3(X4),sK1)) ) | ~spl10_5),
% 1.52/0.57    inference(avatar_component_clause,[],[f117])).
% 1.52/0.57  fof(f117,plain,(
% 1.52/0.57    spl10_5 <=> ! [X4] : (r1_tarski(sK3(X4),sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.52/0.57  fof(f458,plain,(
% 1.52/0.57    r2_hidden(sK5(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f220,f320,f82])).
% 1.52/0.57  fof(f320,plain,(
% 1.52/0.57    r2_hidden(sK5(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK1),k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1))))) | (spl10_1 | ~spl10_6 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f267,f83])).
% 1.52/0.57  fof(f220,plain,(
% 1.52/0.57    r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,k1_tops_1(sK0,sK1)))),sK3(sK5(sK1,k1_tops_1(sK0,sK1)))) | (spl10_1 | ~spl10_7)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f57,f194,f65])).
% 1.52/0.57  fof(f127,plain,(
% 1.52/0.57    spl10_1 | spl10_7),
% 1.52/0.57    inference(avatar_split_clause,[],[f59,f125,f99])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    ( ! [X4] : (m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f123,plain,(
% 1.52/0.57    spl10_1 | spl10_6),
% 1.52/0.57    inference(avatar_split_clause,[],[f60,f121,f99])).
% 1.52/0.57  fof(f60,plain,(
% 1.52/0.57    ( ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f119,plain,(
% 1.52/0.57    spl10_1 | spl10_5),
% 1.52/0.57    inference(avatar_split_clause,[],[f61,f117,f99])).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    ( ! [X4] : (r1_tarski(sK3(X4),sK1) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f115,plain,(
% 1.52/0.57    ~spl10_1 | spl10_4),
% 1.52/0.57    inference(avatar_split_clause,[],[f62,f112,f99])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f110,plain,(
% 1.52/0.57    ~spl10_1 | spl10_3),
% 1.52/0.57    inference(avatar_split_clause,[],[f63,f107,f99])).
% 1.52/0.57  fof(f63,plain,(
% 1.52/0.57    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f105,plain,(
% 1.52/0.57    ~spl10_1 | spl10_2),
% 1.52/0.57    inference(avatar_split_clause,[],[f64,f103,f99])).
% 1.52/0.57  fof(f64,plain,(
% 1.52/0.57    ( ! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (29140)------------------------------
% 1.52/0.57  % (29140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (29140)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (29140)Memory used [KB]: 11001
% 1.52/0.57  % (29140)Time elapsed: 0.173 s
% 1.52/0.57  % (29140)------------------------------
% 1.52/0.57  % (29140)------------------------------
% 1.52/0.59  % (29128)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.60  % (29113)Success in time 0.238 s
%------------------------------------------------------------------------------
