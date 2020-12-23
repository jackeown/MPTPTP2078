%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:38 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 554 expanded)
%              Number of clauses        :   95 ( 161 expanded)
%              Number of leaves         :   14 ( 146 expanded)
%              Depth                    :   19
%              Number of atoms          :  622 (3065 expanded)
%              Number of equality atoms :  112 ( 214 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v4_pre_topc(k1_connsp_2(X0,sK6),X0)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(sK5,X1),sK5)
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ v4_pre_topc(k1_connsp_2(sK5,sK6),sK5)
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f28,f27])).

fof(f51,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( ( k1_connsp_2(X0,X1) = X2
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_connsp_2(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k1_connsp_2(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_connsp_2(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k1_connsp_2(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f17])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_connsp_2(X1,X0) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP0(k1_connsp_2(X1,X0),X1,X0)
      | ~ sP1(X0,X1,k1_connsp_2(X1,X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ? [X3] :
          ( k6_setfam_1(u1_struct_0(X0),X3) = X2
          & ! [X4] :
              ( ( r2_hidden(X4,X3)
              <=> ( r2_hidden(X1,X4)
                  & v4_pre_topc(X4,X0)
                  & v3_pre_topc(X4,X0) ) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f7,f15,f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ( ~ r2_hidden(X1,X4)
                  | ~ v4_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X1,X4)
                    & v4_pre_topc(X4,X0)
                    & v3_pre_topc(X4,X0) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( ( ( r2_hidden(X4,X3)
                    | ~ r2_hidden(X1,X4)
                    | ~ v4_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X4,X0) )
                  & ( ( r2_hidden(X1,X4)
                      & v4_pre_topc(X4,X0)
                      & v3_pre_topc(X4,X0) )
                    | ~ r2_hidden(X4,X3) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ( ~ r2_hidden(X1,X4)
                  | ~ v4_pre_topc(X4,X0)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X1,X4)
                    & v4_pre_topc(X4,X0)
                    & v3_pre_topc(X4,X0) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( ( ( r2_hidden(X4,X3)
                    | ~ r2_hidden(X1,X4)
                    | ~ v4_pre_topc(X4,X0)
                    | ~ v3_pre_topc(X4,X0) )
                  & ( ( r2_hidden(X1,X4)
                      & v4_pre_topc(X4,X0)
                      & v3_pre_topc(X4,X0) )
                    | ~ r2_hidden(X4,X3) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ? [X4] :
                ( ( ~ r2_hidden(X2,X4)
                  | ~ v4_pre_topc(X4,X1)
                  | ~ v3_pre_topc(X4,X1)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X2,X4)
                    & v4_pre_topc(X4,X1)
                    & v3_pre_topc(X4,X1) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ? [X5] :
            ( k6_setfam_1(u1_struct_0(X1),X5) = X0
            & ! [X6] :
                ( ( ( r2_hidden(X6,X5)
                    | ~ r2_hidden(X2,X6)
                    | ~ v4_pre_topc(X6,X1)
                    | ~ v3_pre_topc(X6,X1) )
                  & ( ( r2_hidden(X2,X6)
                      & v4_pre_topc(X6,X1)
                      & v3_pre_topc(X6,X1) )
                    | ~ r2_hidden(X6,X5) ) )
                | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k6_setfam_1(u1_struct_0(X1),X5) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,X5)
                  | ~ r2_hidden(X2,X6)
                  | ~ v4_pre_topc(X6,X1)
                  | ~ v3_pre_topc(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v4_pre_topc(X6,X1)
                    & v3_pre_topc(X6,X1) )
                  | ~ r2_hidden(X6,X5) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( k6_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0
        & ! [X6] :
            ( ( ( r2_hidden(X6,sK3(X0,X1,X2))
                | ~ r2_hidden(X2,X6)
                | ~ v4_pre_topc(X6,X1)
                | ~ v3_pre_topc(X6,X1) )
              & ( ( r2_hidden(X2,X6)
                  & v4_pre_topc(X6,X1)
                  & v3_pre_topc(X6,X1) )
                | ~ r2_hidden(X6,sK3(X0,X1,X2)) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ~ r2_hidden(X2,X4)
            | ~ v4_pre_topc(X4,X1)
            | ~ v3_pre_topc(X4,X1)
            | ~ r2_hidden(X4,X3) )
          & ( ( r2_hidden(X2,X4)
              & v4_pre_topc(X4,X1)
              & v3_pre_topc(X4,X1) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ~ r2_hidden(X2,sK2(X1,X2,X3))
          | ~ v4_pre_topc(sK2(X1,X2,X3),X1)
          | ~ v3_pre_topc(sK2(X1,X2,X3),X1)
          | ~ r2_hidden(sK2(X1,X2,X3),X3) )
        & ( ( r2_hidden(X2,sK2(X1,X2,X3))
            & v4_pre_topc(sK2(X1,X2,X3),X1)
            & v3_pre_topc(sK2(X1,X2,X3),X1) )
          | r2_hidden(sK2(X1,X2,X3),X3) )
        & m1_subset_1(sK2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ( ( ~ r2_hidden(X2,sK2(X1,X2,X3))
                | ~ v4_pre_topc(sK2(X1,X2,X3),X1)
                | ~ v3_pre_topc(sK2(X1,X2,X3),X1)
                | ~ r2_hidden(sK2(X1,X2,X3),X3) )
              & ( ( r2_hidden(X2,sK2(X1,X2,X3))
                  & v4_pre_topc(sK2(X1,X2,X3),X1)
                  & v3_pre_topc(sK2(X1,X2,X3),X1) )
                | r2_hidden(sK2(X1,X2,X3),X3) )
              & m1_subset_1(sK2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ( k6_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,sK3(X0,X1,X2))
                  | ~ r2_hidden(X2,X6)
                  | ~ v4_pre_topc(X6,X1)
                  | ~ v3_pre_topc(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v4_pre_topc(X6,X1)
                    & v3_pre_topc(X6,X1) )
                  | ~ r2_hidden(X6,sK3(X0,X1,X2)) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f23,f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ( ~ v4_pre_topc(sK4(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X6,X2,X0,X1] :
      ( v4_pre_topc(X6,X1)
      | ~ r2_hidden(X6,sK3(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_connsp_2(X1,X0) = X2
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ~ v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3017,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3434,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3017])).

cnf(c_1,plain,
    ( ~ sP1(X0,X1,k1_connsp_2(X1,X0))
    | sP0(k1_connsp_2(X1,X0),X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_280,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_281,plain,
    ( sP1(X0,sK5,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_285,plain,
    ( sP1(X0,sK5,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_281,c_21,c_20])).

cnf(c_326,plain,
    ( sP0(k1_connsp_2(X0,X1),X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | X3 != X1
    | k1_connsp_2(X0,X1) != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_285])).

cnf(c_327,plain,
    ( sP0(k1_connsp_2(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_21,c_20])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | sP0(k1_connsp_2(sK5,X0),sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_21,c_20,c_263])).

cnf(c_332,plain,
    ( sP0(k1_connsp_2(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_3014,plain,
    ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_3437,plain,
    ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3014])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2)
    | k6_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3024,plain,
    ( ~ sP0(X0_46,X0_48,X1_46)
    | k6_setfam_1(u1_struct_0(X0_48),sK3(X0_46,X0_48,X1_46)) = X0_46 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3427,plain,
    ( k6_setfam_1(u1_struct_0(X0_48),sK3(X0_46,X0_48,X1_46)) = X0_46
    | sP0(X0_46,X0_48,X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3024])).

cnf(c_3880,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = k1_connsp_2(sK5,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3437,c_3427])).

cnf(c_4231,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)) = k1_connsp_2(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_3434,c_3880])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3019,plain,
    ( ~ sP0(X0_46,X0_48,X1_46)
    | m1_subset_1(sK3(X0_46,X0_48,X1_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3432,plain,
    ( sP0(X0_46,X0_48,X1_46) != iProver_top
    | m1_subset_1(sK3(X0_46,X0_48,X1_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3019])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v4_pre_topc(sK4(X1,X0),X1)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v4_pre_topc(sK4(X1,X0),X1)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v4_pre_topc(sK4(sK5,X0),sK5)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_399,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ v4_pre_topc(sK4(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_21])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v4_pre_topc(sK4(sK5,X0),sK5)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5) ),
    inference(renaming,[status(thm)],[c_399])).

cnf(c_3011,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v4_pre_topc(sK4(sK5,X0_46),sK5)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) ),
    inference(subtyping,[status(esa)],[c_400])).

cnf(c_3440,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | v4_pre_topc(sK4(sK5,X0_46),sK5) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3011])).

cnf(c_3971,plain,
    ( sP0(X0_46,sK5,X1_46) != iProver_top
    | v4_pre_topc(sK4(sK5,sK3(X0_46,sK5,X1_46)),sK5) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(X0_46,sK5,X1_46)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_3440])).

cnf(c_4311,plain,
    ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
    | v4_pre_topc(sK4(sK5,sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) != iProver_top
    | v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4231,c_3971])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X3,X1)
    | ~ r2_hidden(X3,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3021,plain,
    ( ~ sP0(X0_46,X0_48,X1_46)
    | ~ m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(X0_48)))
    | v4_pre_topc(X2_46,X0_48)
    | ~ r2_hidden(X2_46,sK3(X0_46,X0_48,X1_46)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4099,plain,
    ( ~ sP0(X0_46,sK5,X1_46)
    | ~ m1_subset_1(sK4(sK5,sK3(k1_connsp_2(sK5,X2_46),sK5,X2_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(sK4(sK5,sK3(k1_connsp_2(sK5,X2_46),sK5,X2_46)),sK5)
    | ~ r2_hidden(sK4(sK5,sK3(k1_connsp_2(sK5,X2_46),sK5,X2_46)),sK3(X0_46,sK5,X1_46)) ),
    inference(instantiation,[status(thm)],[c_3021])).

cnf(c_4232,plain,
    ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | ~ m1_subset_1(sK4(sK5,sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(sK4(sK5,sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5)
    | ~ r2_hidden(sK4(sK5,sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) ),
    inference(instantiation,[status(thm)],[c_4099])).

cnf(c_4233,plain,
    ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) != iProver_top
    | m1_subset_1(sK4(sK5,sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v4_pre_topc(sK4(sK5,sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5) = iProver_top
    | r2_hidden(sK4(sK5,sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4232])).

cnf(c_4235,plain,
    ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
    | m1_subset_1(sK4(sK5,sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v4_pre_topc(sK4(sK5,sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top
    | r2_hidden(sK4(sK5,sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4233])).

cnf(c_3037,plain,
    ( ~ v4_pre_topc(X0_46,X0_48)
    | v4_pre_topc(X1_46,X0_48)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_3788,plain,
    ( v4_pre_topc(X0_46,sK5)
    | ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5)
    | X0_46 != k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)) ),
    inference(instantiation,[status(thm)],[c_3037])).

cnf(c_4016,plain,
    ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5)
    | v4_pre_topc(k1_connsp_2(sK5,X1_46),sK5)
    | k1_connsp_2(sK5,X1_46) != k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) ),
    inference(instantiation,[status(thm)],[c_3788])).

cnf(c_4017,plain,
    ( k1_connsp_2(sK5,X0_46) != k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5) != iProver_top
    | v4_pre_topc(k1_connsp_2(sK5,X0_46),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4016])).

cnf(c_4019,plain,
    ( k1_connsp_2(sK5,sK6) != k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) != iProver_top
    | v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4017])).

cnf(c_0,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k1_connsp_2(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_308,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X4,u1_struct_0(sK5))
    | X4 != X2
    | X3 != X0
    | k1_connsp_2(X1,X2) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_285])).

cnf(c_309,plain,
    ( ~ sP0(X0,sK5,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | k1_connsp_2(sK5,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_3015,plain,
    ( ~ sP0(X0_46,sK5,X1_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK5))
    | k1_connsp_2(sK5,X1_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_3808,plain,
    ( ~ sP0(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK5))
    | ~ m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_connsp_2(sK5,X1_46) = k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) ),
    inference(instantiation,[status(thm)],[c_3015])).

cnf(c_3810,plain,
    ( ~ sP0(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5,sK6)
    | ~ m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k1_connsp_2(sK5,sK6) = k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3808])).

cnf(c_3034,plain,
    ( ~ sP0(X0_46,X0_48,X1_46)
    | sP0(X2_46,X0_48,X1_46)
    | X2_46 != X0_46 ),
    theory(equality)).

cnf(c_3657,plain,
    ( sP0(X0_46,sK5,X1_46)
    | ~ sP0(k1_connsp_2(sK5,X1_46),sK5,X1_46)
    | X0_46 != k1_connsp_2(sK5,X1_46) ),
    inference(instantiation,[status(thm)],[c_3034])).

cnf(c_3748,plain,
    ( sP0(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5,X0_46)
    | ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != k1_connsp_2(sK5,X0_46) ),
    inference(instantiation,[status(thm)],[c_3657])).

cnf(c_3750,plain,
    ( sP0(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5,sK6)
    | ~ sP0(k1_connsp_2(sK5,sK6),sK5,sK6)
    | k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)) != k1_connsp_2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3748])).

cnf(c_3039,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X0_47)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_3620,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k1_connsp_2(sK5,X1_46),k1_zfmisc_1(u1_struct_0(sK5)))
    | X0_46 != k1_connsp_2(sK5,X1_46) ),
    inference(instantiation,[status(thm)],[c_3039])).

cnf(c_3736,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k1_connsp_2(sK5,X0_46),k1_zfmisc_1(u1_struct_0(sK5)))
    | k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != k1_connsp_2(sK5,X0_46) ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_3738,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k1_connsp_2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)) != k1_connsp_2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3736])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | r2_hidden(sK4(X1,X0),X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | r2_hidden(sK4(X1,X0),X0)
    | ~ v2_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | r2_hidden(sK4(sK5,X0),X0)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_378,plain,
    ( r2_hidden(sK4(sK5,X0),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_21])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | r2_hidden(sK4(sK5,X0),X0) ),
    inference(renaming,[status(thm)],[c_378])).

cnf(c_3012,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5)
    | r2_hidden(sK4(sK5,X0_46),X0_46) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_3696,plain,
    ( ~ m1_subset_1(sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5)
    | r2_hidden(sK4(sK5,sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) ),
    inference(instantiation,[status(thm)],[c_3012])).

cnf(c_3702,plain,
    ( m1_subset_1(sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) = iProver_top
    | r2_hidden(sK4(sK5,sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3696])).

cnf(c_3704,plain,
    ( m1_subset_1(sK3(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top
    | r2_hidden(sK4(sK5,sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3702])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK4(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK4(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK4(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_357,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | m1_subset_1(sK4(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_21])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK4(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5) ),
    inference(renaming,[status(thm)],[c_357])).

cnf(c_3013,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK4(sK5,X0_46),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) ),
    inference(subtyping,[status(esa)],[c_358])).

cnf(c_3697,plain,
    ( ~ m1_subset_1(sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK4(sK5,sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) ),
    inference(instantiation,[status(thm)],[c_3013])).

cnf(c_3698,plain,
    ( m1_subset_1(sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK4(sK5,sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3697])).

cnf(c_3700,plain,
    ( m1_subset_1(sK3(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK4(sK5,sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3698])).

cnf(c_3630,plain,
    ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = k1_connsp_2(sK5,X0_46) ),
    inference(instantiation,[status(thm)],[c_3024])).

cnf(c_3632,plain,
    ( ~ sP0(k1_connsp_2(sK5,sK6),sK5,sK6)
    | k6_setfam_1(u1_struct_0(sK5),sK3(k1_connsp_2(sK5,sK6),sK5,sK6)) = k1_connsp_2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3630])).

cnf(c_3625,plain,
    ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | m1_subset_1(sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_3019])).

cnf(c_3626,plain,
    ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) != iProver_top
    | m1_subset_1(sK3(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3625])).

cnf(c_3628,plain,
    ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
    | m1_subset_1(sK3(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3626])).

cnf(c_3090,plain,
    ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3014])).

cnf(c_3092,plain,
    ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_3091,plain,
    ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3014])).

cnf(c_3016,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(sK5))
    | m1_subset_1(k1_connsp_2(sK5,X0_46),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_267])).

cnf(c_3085,plain,
    ( m1_subset_1(k1_connsp_2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3016])).

cnf(c_18,negated_conjecture,
    ( ~ v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,plain,
    ( v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_26,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4311,c_4235,c_4019,c_3810,c_3750,c_3738,c_3704,c_3700,c_3632,c_3628,c_3092,c_3091,c_3085,c_27,c_26,c_19])).


%------------------------------------------------------------------------------
