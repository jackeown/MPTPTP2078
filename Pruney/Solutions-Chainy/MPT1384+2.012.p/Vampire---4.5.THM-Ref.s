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
% DateTime   : Thu Dec  3 13:15:07 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  134 (1973 expanded)
%              Number of leaves         :   16 ( 620 expanded)
%              Depth                    :   43
%              Number of atoms          :  683 (19861 expanded)
%              Number of equality atoms :   28 ( 177 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1374,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1373,f1151])).

fof(f1151,plain,(
    r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f1148,f58])).

fof(f58,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1) ),
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

fof(f1148,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1147,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f1147,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1146,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f1146,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1138,f53])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f1138,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(trivial_inequality_removal,[],[f1137])).

fof(f1137,plain,
    ( sK1 != sK1
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f85,f1094])).

fof(f1094,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1091,f53])).

fof(f1091,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f1090])).

fof(f1090,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f1060,f298])).

fof(f298,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = X0 ) ),
    inference(condensation,[],[f297])).

fof(f297,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k1_tops_1(sK0,X0) = X0 ) ),
    inference(resolution,[],[f296,f52])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,X1)
      | k1_tops_1(X1,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f295,f52])).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(sK0)
      | k1_tops_1(X1,X0) = X0 ) ),
    inference(resolution,[],[f65,f51])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X1,X3) = X3 ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f1060,plain,
    ( v3_pre_topc(sK1,sK0)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f1059,f93])).

fof(f93,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f91,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f90,f53])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f60,f52])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
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

fof(f1059,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1058,f91])).

fof(f1058,plain,
    ( v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f1057,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1057,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1056,f82])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1056,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f1049,f80])).

fof(f1049,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1041])).

fof(f1041,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f1040,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK5(X0,X1,X2),X2)
            & r2_hidden(sK5(X0,X1,X2),X1)
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f1040,plain,
    ( r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f1028])).

fof(f1028,plain,
    ( v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f1027,f588])).

fof(f588,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))),X0)
      | r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),X0)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f332,f80])).

fof(f332,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(X1))
      | v3_pre_topc(sK1,sK0)
      | r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),X1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f308,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f308,plain,
    ( r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f306,f91])).

fof(f306,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(sK1,X1)
      | r2_hidden(sK5(sK1,sK1,X1),k1_tops_1(sK0,sK3(sK5(sK1,sK1,X1))))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f288,f82])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,X0)
      | v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X1)
      | r2_hidden(sK5(X0,sK1,X1),k1_tops_1(sK0,sK3(sK5(X0,sK1,X1))))
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f286,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,sK1,X1),u1_struct_0(sK0))
      | ~ r1_tarski(X1,X0)
      | r1_tarski(sK1,X1)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f122,f53])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X3))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X1)
      | m1_subset_1(sK5(X2,X0,X1),X3) ) ),
    inference(resolution,[],[f114,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f114,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3),X2)
      | r1_tarski(X2,X3)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X3,X1) ) ),
    inference(resolution,[],[f104,f80])).

fof(f104,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X1))
      | r2_hidden(sK5(X1,X2,X3),X2)
      | r1_tarski(X2,X3)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f74,f80])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f286,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,sK1,X1),k1_tops_1(sK0,sK3(sK5(X0,sK1,X1))))
      | ~ m1_subset_1(sK5(X0,sK1,X1),u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X1)
      | ~ r1_tarski(sK1,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f284,f114])).

fof(f284,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,k1_tops_1(sK0,sK3(X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f283,f54])).

fof(f54,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f283,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k1_tops_1(sK0,sK3(X0)))
      | ~ r2_hidden(X0,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k1_tops_1(sK0,sK3(X0)))
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f281,f55])).

fof(f55,plain,(
    ! [X4] :
      ( m1_connsp_2(sK3(X4),sK0,X4)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f280,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f280,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f279,f52])).

fof(f279,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | r2_hidden(X1,k1_tops_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f51])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f1027,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f400,f483])).

fof(f483,plain,
    ( r1_tarski(sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))),u1_struct_0(sK0))
    | v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f469,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f469,plain,
    ( m1_subset_1(sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f467,f91])).

fof(f467,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(sK1,X1)
      | m1_subset_1(sK3(sK5(sK1,sK1,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f465,f82])).

fof(f465,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(sK1,X9)
      | r1_tarski(sK1,X8)
      | ~ r1_tarski(X8,X9)
      | m1_subset_1(sK3(sK5(X9,sK1,X8)),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f124,f140])).

fof(f124,plain,(
    ! [X8,X9] :
      ( r1_tarski(sK1,X8)
      | ~ r1_tarski(sK1,X9)
      | ~ r1_tarski(X8,X9)
      | m1_subset_1(sK3(sK5(X9,sK1,X8)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK5(X9,sK1,X8),u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f114,f54])).

fof(f400,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f394,f233])).

fof(f233,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f221,f53])).

fof(f221,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k1_tops_1(sK0,X2),k1_tops_1(sK0,X1))
      | ~ r1_tarski(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f219,f80])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f61,f52])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f394,plain,
    ( r1_tarski(sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))),sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f392,f91])).

fof(f392,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(sK1,X1)
      | r1_tarski(sK3(sK5(sK1,sK1,X1)),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f390,f82])).

fof(f390,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(sK1,X11)
      | r1_tarski(sK1,X10)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(sK3(sK5(X11,sK1,X10)),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f125,f140])).

fof(f125,plain,(
    ! [X10,X11] :
      ( r1_tarski(sK1,X10)
      | ~ r1_tarski(sK1,X11)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(sK3(sK5(X11,sK1,X10)),sK1)
      | ~ m1_subset_1(sK5(X11,sK1,X10),u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f114,f56])).

fof(f56,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | r1_tarski(sK3(X4),sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X1,X0) != X0
      | v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1)
      | k1_tops_1(X1,X0) != X0
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(condensation,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1373,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f1372,f82])).

fof(f1372,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f1370,f53])).

fof(f1370,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f1149,f1156])).

fof(f1156,plain,(
    ! [X3] :
      ( m1_connsp_2(sK1,sK0,X3)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(subsumption_resolution,[],[f1153,f53])).

fof(f1153,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(sK1,sK0,X3) ) ),
    inference(resolution,[],[f1148,f336])).

fof(f336,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f335,f50])).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f334,f52])).

fof(f334,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m1_connsp_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f333,f51])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X1,X0,X2)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f64,f81])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f1149,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f1148,f59])).

fof(f59,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(sK1,sK0)
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,sK1) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (4141)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.49  % (4147)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.49  % (4135)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.49  % (4153)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.49  % (4135)Refutation not found, incomplete strategy% (4135)------------------------------
% 0.19/0.49  % (4135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (4157)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.50  % (4135)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (4135)Memory used [KB]: 10618
% 0.19/0.50  % (4135)Time elapsed: 0.097 s
% 0.19/0.50  % (4135)------------------------------
% 0.19/0.50  % (4135)------------------------------
% 0.19/0.50  % (4145)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.50  % (4152)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.50  % (4149)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.50  % (4143)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.50  % (4140)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.50  % (4137)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.50  % (4136)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (4150)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.50  % (4140)Refutation not found, incomplete strategy% (4140)------------------------------
% 0.19/0.50  % (4140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (4140)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (4140)Memory used [KB]: 6140
% 0.19/0.50  % (4140)Time elapsed: 0.100 s
% 0.19/0.50  % (4140)------------------------------
% 0.19/0.50  % (4140)------------------------------
% 0.19/0.51  % (4148)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (4151)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.51  % (4148)Refutation not found, incomplete strategy% (4148)------------------------------
% 0.19/0.51  % (4148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (4148)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (4148)Memory used [KB]: 6140
% 0.19/0.51  % (4148)Time elapsed: 0.110 s
% 0.19/0.51  % (4148)------------------------------
% 0.19/0.51  % (4148)------------------------------
% 0.19/0.51  % (4144)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.51  % (4146)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.51  % (4141)Refutation not found, incomplete strategy% (4141)------------------------------
% 0.19/0.51  % (4141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (4141)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (4141)Memory used [KB]: 10618
% 0.19/0.51  % (4141)Time elapsed: 0.101 s
% 0.19/0.51  % (4141)------------------------------
% 0.19/0.51  % (4141)------------------------------
% 0.19/0.51  % (4142)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.51  % (4142)Refutation not found, incomplete strategy% (4142)------------------------------
% 0.19/0.51  % (4142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (4142)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (4142)Memory used [KB]: 1663
% 0.19/0.51  % (4142)Time elapsed: 0.103 s
% 0.19/0.51  % (4142)------------------------------
% 0.19/0.51  % (4142)------------------------------
% 0.19/0.52  % (4154)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.52  % (4156)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.52  % (4138)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.52  % (4139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.52  % (4155)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.52  % (4158)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.52  % (4159)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.53  % (4160)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.21/0.64  % (4144)Refutation not found, incomplete strategy% (4144)------------------------------
% 2.21/0.64  % (4144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.64  % (4144)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.64  
% 2.21/0.64  % (4144)Memory used [KB]: 6140
% 2.21/0.64  % (4144)Time elapsed: 0.189 s
% 2.21/0.64  % (4144)------------------------------
% 2.21/0.64  % (4144)------------------------------
% 2.21/0.65  % (4156)Refutation found. Thanks to Tanya!
% 2.21/0.65  % SZS status Theorem for theBenchmark
% 2.21/0.65  % SZS output start Proof for theBenchmark
% 2.21/0.65  fof(f1374,plain,(
% 2.21/0.65    $false),
% 2.21/0.65    inference(subsumption_resolution,[],[f1373,f1151])).
% 2.21/0.65  fof(f1151,plain,(
% 2.21/0.65    r2_hidden(sK2,sK1)),
% 2.21/0.65    inference(resolution,[],[f1148,f58])).
% 2.21/0.65  fof(f58,plain,(
% 2.21/0.65    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1)),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f39,plain,(
% 2.21/0.65    (((! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & (! [X4] : ((r1_tarski(sK3(X4),sK1) & m1_connsp_2(sK3(X4),sK0,X4) & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37,f36,f35])).
% 2.21/0.65  fof(f35,plain,(
% 2.21/0.65    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f36,plain,(
% 2.21/0.65    ? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f37,plain,(
% 2.21/0.65    ? [X2] : (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f38,plain,(
% 2.21/0.65    ! [X4] : (? [X5] : (r1_tarski(X5,sK1) & m1_connsp_2(X5,sK0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) => (r1_tarski(sK3(X4),sK1) & m1_connsp_2(sK3(X4),sK0,X4) & m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f34,plain,(
% 2.21/0.65    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.21/0.65    inference(rectify,[],[f33])).
% 2.21/0.65  fof(f33,plain,(
% 2.21/0.65    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.21/0.65    inference(flattening,[],[f32])).
% 2.21/0.65  fof(f32,plain,(
% 2.21/0.65    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.21/0.65    inference(nnf_transformation,[],[f15])).
% 2.21/0.65  fof(f15,plain,(
% 2.21/0.65    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.21/0.65    inference(flattening,[],[f14])).
% 2.21/0.65  fof(f14,plain,(
% 2.21/0.65    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f13])).
% 2.21/0.65  fof(f13,negated_conjecture,(
% 2.21/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.21/0.65    inference(negated_conjecture,[],[f12])).
% 2.21/0.65  fof(f12,conjecture,(
% 2.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 2.21/0.65  fof(f1148,plain,(
% 2.21/0.65    v3_pre_topc(sK1,sK0)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1147,f51])).
% 2.21/0.65  fof(f51,plain,(
% 2.21/0.65    v2_pre_topc(sK0)),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f1147,plain,(
% 2.21/0.65    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1146,f52])).
% 2.21/0.65  fof(f52,plain,(
% 2.21/0.65    l1_pre_topc(sK0)),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f1146,plain,(
% 2.21/0.65    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1138,f53])).
% 2.21/0.65  fof(f53,plain,(
% 2.21/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f1138,plain,(
% 2.21/0.65    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.21/0.65    inference(trivial_inequality_removal,[],[f1137])).
% 2.21/0.65  fof(f1137,plain,(
% 2.21/0.65    sK1 != sK1 | v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.21/0.65    inference(superposition,[],[f85,f1094])).
% 2.21/0.65  fof(f1094,plain,(
% 2.21/0.65    sK1 = k1_tops_1(sK0,sK1)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1091,f53])).
% 2.21/0.65  fof(f1091,plain,(
% 2.21/0.65    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.65    inference(duplicate_literal_removal,[],[f1090])).
% 2.21/0.65  fof(f1090,plain,(
% 2.21/0.65    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1)),
% 2.21/0.65    inference(resolution,[],[f1060,f298])).
% 2.21/0.65  fof(f298,plain,(
% 2.21/0.65    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = X0) )),
% 2.21/0.65    inference(condensation,[],[f297])).
% 2.21/0.65  fof(f297,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k1_tops_1(sK0,X0) = X0) )),
% 2.21/0.65    inference(resolution,[],[f296,f52])).
% 2.21/0.65  fof(f296,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,X1) | k1_tops_1(X1,X0) = X0) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f295,f52])).
% 2.21/0.65  fof(f295,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK0) | k1_tops_1(X1,X0) = X0) )),
% 2.21/0.65    inference(resolution,[],[f65,f51])).
% 2.21/0.65  fof(f65,plain,(
% 2.21/0.65    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | k1_tops_1(X1,X3) = X3) )),
% 2.21/0.65    inference(cnf_transformation,[],[f24])).
% 2.21/0.65  fof(f24,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.65    inference(flattening,[],[f23])).
% 2.21/0.65  fof(f23,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f9])).
% 2.21/0.65  fof(f9,axiom,(
% 2.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 2.21/0.65  fof(f1060,plain,(
% 2.21/0.65    v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1)),
% 2.21/0.65    inference(resolution,[],[f1059,f93])).
% 2.21/0.65  fof(f93,plain,(
% 2.21/0.65    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 2.21/0.65    inference(resolution,[],[f91,f78])).
% 2.21/0.65  fof(f78,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.21/0.65    inference(cnf_transformation,[],[f48])).
% 2.21/0.65  fof(f48,plain,(
% 2.21/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.65    inference(flattening,[],[f47])).
% 2.21/0.65  fof(f47,plain,(
% 2.21/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.65    inference(nnf_transformation,[],[f1])).
% 2.21/0.65  fof(f1,axiom,(
% 2.21/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.21/0.65  fof(f91,plain,(
% 2.21/0.65    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.21/0.65    inference(resolution,[],[f90,f53])).
% 2.21/0.65  fof(f90,plain,(
% 2.21/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 2.21/0.65    inference(resolution,[],[f60,f52])).
% 2.21/0.65  fof(f60,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f16])).
% 2.21/0.65  fof(f16,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f6])).
% 2.21/0.65  fof(f6,axiom,(
% 2.21/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.21/0.65  fof(f1059,plain,(
% 2.21/0.65    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1058,f91])).
% 2.21/0.65  fof(f1058,plain,(
% 2.21/0.65    v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.21/0.65    inference(resolution,[],[f1057,f80])).
% 2.21/0.65  fof(f80,plain,(
% 2.21/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f49])).
% 2.21/0.65  fof(f49,plain,(
% 2.21/0.65    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.21/0.65    inference(nnf_transformation,[],[f4])).
% 2.21/0.65  fof(f4,axiom,(
% 2.21/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.21/0.65  fof(f1057,plain,(
% 2.21/0.65    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.21/0.65    inference(subsumption_resolution,[],[f1056,f82])).
% 2.21/0.65  fof(f82,plain,(
% 2.21/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.21/0.65    inference(equality_resolution,[],[f77])).
% 2.21/0.65  fof(f77,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.21/0.65    inference(cnf_transformation,[],[f48])).
% 2.21/0.65  fof(f1056,plain,(
% 2.21/0.65    v3_pre_topc(sK1,sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 2.21/0.65    inference(resolution,[],[f1049,f80])).
% 2.21/0.65  fof(f1049,plain,(
% 2.21/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.21/0.65    inference(duplicate_literal_removal,[],[f1041])).
% 2.21/0.65  fof(f1041,plain,(
% 2.21/0.65    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 2.21/0.65    inference(resolution,[],[f1040,f75])).
% 2.21/0.65  fof(f75,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f46])).
% 2.21/0.65  fof(f46,plain,(
% 2.21/0.65    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f45])).
% 2.21/0.65  fof(f45,plain,(
% 2.21/0.65    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),X0)))),
% 2.21/0.65    introduced(choice_axiom,[])).
% 2.21/0.65  fof(f29,plain,(
% 2.21/0.65    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.65    inference(flattening,[],[f28])).
% 2.21/0.65  fof(f28,plain,(
% 2.21/0.65    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f3])).
% 2.21/0.65  fof(f3,axiom,(
% 2.21/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 2.21/0.65  fof(f1040,plain,(
% 2.21/0.65    r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.21/0.65    inference(duplicate_literal_removal,[],[f1028])).
% 2.21/0.65  fof(f1028,plain,(
% 2.21/0.65    v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.21/0.65    inference(resolution,[],[f1027,f588])).
% 2.21/0.65  fof(f588,plain,(
% 2.21/0.65    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))),X0) | r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),X0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(resolution,[],[f332,f80])).
% 2.21/0.65  fof(f332,plain,(
% 2.21/0.65    ( ! [X1] : (~m1_subset_1(k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))),k1_zfmisc_1(X1)) | v3_pre_topc(sK1,sK0) | r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),X1) | r1_tarski(sK1,k1_tops_1(sK0,sK1))) )),
% 2.21/0.65    inference(resolution,[],[f308,f72])).
% 2.21/0.65  fof(f72,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f27])).
% 2.21/0.65  fof(f27,plain,(
% 2.21/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f2])).
% 2.21/0.65  fof(f2,axiom,(
% 2.21/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.21/0.65  fof(f308,plain,(
% 2.21/0.65    r2_hidden(sK5(sK1,sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.21/0.65    inference(resolution,[],[f306,f91])).
% 2.21/0.65  fof(f306,plain,(
% 2.21/0.65    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(sK1,X1) | r2_hidden(sK5(sK1,sK1,X1),k1_tops_1(sK0,sK3(sK5(sK1,sK1,X1)))) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(resolution,[],[f288,f82])).
% 2.21/0.65  fof(f288,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X1) | r2_hidden(sK5(X0,sK1,X1),k1_tops_1(sK0,sK3(sK5(X0,sK1,X1)))) | ~r1_tarski(X1,X0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f286,f140])).
% 2.21/0.65  fof(f140,plain,(
% 2.21/0.65    ( ! [X0,X1] : (m1_subset_1(sK5(X0,sK1,X1),u1_struct_0(sK0)) | ~r1_tarski(X1,X0) | r1_tarski(sK1,X1) | ~r1_tarski(sK1,X0)) )),
% 2.21/0.65    inference(resolution,[],[f122,f53])).
% 2.21/0.65  fof(f122,plain,(
% 2.21/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X3)) | ~r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | r1_tarski(X0,X1) | m1_subset_1(sK5(X2,X0,X1),X3)) )),
% 2.21/0.65    inference(resolution,[],[f114,f81])).
% 2.21/0.65  fof(f81,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f31])).
% 2.21/0.65  fof(f31,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.21/0.65    inference(flattening,[],[f30])).
% 2.21/0.65  fof(f30,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.21/0.65    inference(ennf_transformation,[],[f5])).
% 2.21/0.65  fof(f5,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.21/0.65  fof(f114,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (r2_hidden(sK5(X1,X2,X3),X2) | r1_tarski(X2,X3) | ~r1_tarski(X2,X1) | ~r1_tarski(X3,X1)) )),
% 2.21/0.65    inference(resolution,[],[f104,f80])).
% 2.21/0.65  fof(f104,plain,(
% 2.21/0.65    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(X1)) | r2_hidden(sK5(X1,X2,X3),X2) | r1_tarski(X2,X3) | ~r1_tarski(X2,X1)) )),
% 2.21/0.65    inference(resolution,[],[f74,f80])).
% 2.21/0.65  fof(f74,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f46])).
% 2.21/0.65  fof(f286,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r2_hidden(sK5(X0,sK1,X1),k1_tops_1(sK0,sK3(sK5(X0,sK1,X1)))) | ~m1_subset_1(sK5(X0,sK1,X1),u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X1) | ~r1_tarski(sK1,X0) | ~r1_tarski(X1,X0)) )),
% 2.21/0.65    inference(resolution,[],[f284,f114])).
% 2.21/0.65  fof(f284,plain,(
% 2.21/0.65    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k1_tops_1(sK0,sK3(X0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f283,f54])).
% 2.21/0.65  fof(f54,plain,(
% 2.21/0.65    ( ! [X4] : (~r2_hidden(X4,sK1) | m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f283,plain,(
% 2.21/0.65    ( ! [X0] : (~m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_tops_1(sK0,sK3(X0))) | ~r2_hidden(X0,sK1) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(duplicate_literal_removal,[],[f282])).
% 2.21/0.65  fof(f282,plain,(
% 2.21/0.65    ( ! [X0] : (~m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_tops_1(sK0,sK3(X0))) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(resolution,[],[f281,f55])).
% 2.21/0.65  fof(f55,plain,(
% 2.21/0.65    ( ! [X4] : (m1_connsp_2(sK3(X4),sK0,X4) | ~r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f281,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f280,f50])).
% 2.21/0.65  fof(f50,plain,(
% 2.21/0.65    ~v2_struct_0(sK0)),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f280,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f279,f52])).
% 2.21/0.65  fof(f279,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 2.21/0.65    inference(resolution,[],[f62,f51])).
% 2.21/0.65  fof(f62,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | v2_struct_0(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f40])).
% 2.21/0.65  fof(f40,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.65    inference(nnf_transformation,[],[f20])).
% 2.21/0.65  fof(f20,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.65    inference(flattening,[],[f19])).
% 2.21/0.65  fof(f19,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f10])).
% 2.21/0.65  fof(f10,axiom,(
% 2.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 2.21/0.65  fof(f1027,plain,(
% 2.21/0.65    r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.21/0.65    inference(subsumption_resolution,[],[f400,f483])).
% 2.21/0.65  fof(f483,plain,(
% 2.21/0.65    r1_tarski(sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))),u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.21/0.65    inference(resolution,[],[f469,f79])).
% 2.21/0.65  fof(f79,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f49])).
% 2.21/0.65  fof(f469,plain,(
% 2.21/0.65    m1_subset_1(sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.21/0.65    inference(resolution,[],[f467,f91])).
% 2.21/0.65  fof(f467,plain,(
% 2.21/0.65    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(sK1,X1) | m1_subset_1(sK3(sK5(sK1,sK1,X1)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(resolution,[],[f465,f82])).
% 2.21/0.65  fof(f465,plain,(
% 2.21/0.65    ( ! [X8,X9] : (~r1_tarski(sK1,X9) | r1_tarski(sK1,X8) | ~r1_tarski(X8,X9) | m1_subset_1(sK3(sK5(X9,sK1,X8)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f124,f140])).
% 2.21/0.65  fof(f124,plain,(
% 2.21/0.65    ( ! [X8,X9] : (r1_tarski(sK1,X8) | ~r1_tarski(sK1,X9) | ~r1_tarski(X8,X9) | m1_subset_1(sK3(sK5(X9,sK1,X8)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK5(X9,sK1,X8),u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(resolution,[],[f114,f54])).
% 2.21/0.65  fof(f400,plain,(
% 2.21/0.65    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(k1_tops_1(sK0,sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1)) | ~r1_tarski(sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))),u1_struct_0(sK0))),
% 2.21/0.65    inference(resolution,[],[f394,f233])).
% 2.21/0.65  fof(f233,plain,(
% 2.21/0.65    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 2.21/0.65    inference(resolution,[],[f221,f53])).
% 2.21/0.65  fof(f221,plain,(
% 2.21/0.65    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,X1) | r1_tarski(k1_tops_1(sK0,X2),k1_tops_1(sK0,X1)) | ~r1_tarski(X2,u1_struct_0(sK0))) )),
% 2.21/0.65    inference(resolution,[],[f219,f80])).
% 2.21/0.65  fof(f219,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) )),
% 2.21/0.65    inference(resolution,[],[f61,f52])).
% 2.21/0.65  fof(f61,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f18])).
% 2.21/0.65  fof(f18,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.65    inference(flattening,[],[f17])).
% 2.21/0.65  fof(f17,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f7])).
% 2.21/0.65  fof(f7,axiom,(
% 2.21/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 2.21/0.65  fof(f394,plain,(
% 2.21/0.65    r1_tarski(sK3(sK5(sK1,sK1,k1_tops_1(sK0,sK1))),sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.21/0.65    inference(resolution,[],[f392,f91])).
% 2.21/0.65  fof(f392,plain,(
% 2.21/0.65    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(sK1,X1) | r1_tarski(sK3(sK5(sK1,sK1,X1)),sK1) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(resolution,[],[f390,f82])).
% 2.21/0.65  fof(f390,plain,(
% 2.21/0.65    ( ! [X10,X11] : (~r1_tarski(sK1,X11) | r1_tarski(sK1,X10) | ~r1_tarski(X10,X11) | r1_tarski(sK3(sK5(X11,sK1,X10)),sK1) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f125,f140])).
% 2.21/0.65  fof(f125,plain,(
% 2.21/0.65    ( ! [X10,X11] : (r1_tarski(sK1,X10) | ~r1_tarski(sK1,X11) | ~r1_tarski(X10,X11) | r1_tarski(sK3(sK5(X11,sK1,X10)),sK1) | ~m1_subset_1(sK5(X11,sK1,X10),u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(resolution,[],[f114,f56])).
% 2.21/0.65  fof(f56,plain,(
% 2.21/0.65    ( ! [X4] : (~r2_hidden(X4,sK1) | r1_tarski(sK3(X4),sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v3_pre_topc(sK1,sK0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f85,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k1_tops_1(X1,X0) != X0 | v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.21/0.65    inference(duplicate_literal_removal,[],[f84])).
% 2.21/0.65  fof(f84,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(X0,X1) | k1_tops_1(X1,X0) != X0 | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.21/0.65    inference(condensation,[],[f66])).
% 2.21/0.65  fof(f66,plain,(
% 2.21/0.65    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f24])).
% 2.21/0.65  fof(f1373,plain,(
% 2.21/0.65    ~r2_hidden(sK2,sK1)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1372,f82])).
% 2.21/0.65  fof(f1372,plain,(
% 2.21/0.65    ~r1_tarski(sK1,sK1) | ~r2_hidden(sK2,sK1)),
% 2.21/0.65    inference(subsumption_resolution,[],[f1370,f53])).
% 2.21/0.65  fof(f1370,plain,(
% 2.21/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,sK1) | ~r2_hidden(sK2,sK1)),
% 2.21/0.65    inference(resolution,[],[f1149,f1156])).
% 2.21/0.65  fof(f1156,plain,(
% 2.21/0.65    ( ! [X3] : (m1_connsp_2(sK1,sK0,X3) | ~r2_hidden(X3,sK1)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f1153,f53])).
% 2.21/0.65  fof(f1153,plain,(
% 2.21/0.65    ( ! [X3] : (~r2_hidden(X3,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK1,sK0,X3)) )),
% 2.21/0.65    inference(resolution,[],[f1148,f336])).
% 2.21/0.65  fof(f336,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v3_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,X0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f335,f50])).
% 2.21/0.65  fof(f335,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f334,f52])).
% 2.21/0.65  fof(f334,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 2.21/0.65    inference(resolution,[],[f333,f51])).
% 2.21/0.65  fof(f333,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_connsp_2(X1,X0,X2) | v2_struct_0(X0)) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f64,f81])).
% 2.21/0.65  fof(f64,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f22,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.21/0.65    inference(flattening,[],[f21])).
% 2.21/0.65  fof(f21,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f11])).
% 2.21/0.65  fof(f11,axiom,(
% 2.21/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 2.21/0.65  fof(f1149,plain,(
% 2.21/0.65    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) )),
% 2.21/0.65    inference(resolution,[],[f1148,f59])).
% 2.21/0.65  fof(f59,plain,(
% 2.21/0.65    ( ! [X3] : (~v3_pre_topc(sK1,sK0) | ~m1_connsp_2(X3,sK0,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (4156)------------------------------
% 2.21/0.65  % (4156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (4156)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (4156)Memory used [KB]: 7547
% 2.21/0.65  % (4156)Time elapsed: 0.249 s
% 2.21/0.65  % (4156)------------------------------
% 2.21/0.65  % (4156)------------------------------
% 2.21/0.65  % (4134)Success in time 0.293 s
%------------------------------------------------------------------------------
