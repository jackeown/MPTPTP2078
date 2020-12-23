%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:47 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
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

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_connsp_2(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k1_connsp_2(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_connsp_2(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k1_connsp_2(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_connsp_2(X1,X0) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP0(k1_connsp_2(X1,X0),X1,X0)
      | ~ sP1(X0,X1,k1_connsp_2(X1,X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(definition_folding,[],[f9,f15,f14])).

fof(f46,plain,(
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

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f25,plain,(
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
     => ( k6_setfam_1(u1_struct_0(X1),sK4(X0,X1,X2)) = X0
        & ! [X6] :
            ( ( ( r2_hidden(X6,sK4(X0,X1,X2))
                | ~ r2_hidden(X2,X6)
                | ~ v4_pre_topc(X6,X1)
                | ~ v3_pre_topc(X6,X1) )
              & ( ( r2_hidden(X2,X6)
                  & v4_pre_topc(X6,X1)
                  & v3_pre_topc(X6,X1) )
                | ~ r2_hidden(X6,sK4(X0,X1,X2)) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
     => ( ( ~ r2_hidden(X2,sK3(X1,X2,X3))
          | ~ v4_pre_topc(sK3(X1,X2,X3),X1)
          | ~ v3_pre_topc(sK3(X1,X2,X3),X1)
          | ~ r2_hidden(sK3(X1,X2,X3),X3) )
        & ( ( r2_hidden(X2,sK3(X1,X2,X3))
            & v4_pre_topc(sK3(X1,X2,X3),X1)
            & v3_pre_topc(sK3(X1,X2,X3),X1) )
          | r2_hidden(sK3(X1,X2,X3),X3) )
        & m1_subset_1(sK3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ( ( ~ r2_hidden(X2,sK3(X1,X2,X3))
                | ~ v4_pre_topc(sK3(X1,X2,X3),X1)
                | ~ v3_pre_topc(sK3(X1,X2,X3),X1)
                | ~ r2_hidden(sK3(X1,X2,X3),X3) )
              & ( ( r2_hidden(X2,sK3(X1,X2,X3))
                  & v4_pre_topc(sK3(X1,X2,X3),X1)
                  & v3_pre_topc(sK3(X1,X2,X3),X1) )
                | r2_hidden(sK3(X1,X2,X3),X3) )
              & m1_subset_1(sK3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ( k6_setfam_1(u1_struct_0(X1),sK4(X0,X1,X2)) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,sK4(X0,X1,X2))
                  | ~ r2_hidden(X2,X6)
                  | ~ v4_pre_topc(X6,X1)
                  | ~ v3_pre_topc(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v4_pre_topc(X6,X1)
                    & v3_pre_topc(X6,X1) )
                  | ~ r2_hidden(X6,sK4(X0,X1,X2)) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X1),sK4(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
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

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ( ~ v4_pre_topc(sK2(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( v4_pre_topc(X6,X1)
      | ~ r2_hidden(X6,sK4(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_connsp_2(X1,X0) = X2
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

cnf(c_4,plain,
    ( ~ sP1(X0,X1,k1_connsp_2(X1,X0))
    | sP0(k1_connsp_2(X1,X0),X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

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
    inference(resolution_lifted,[status(thm)],[c_4,c_285])).

cnf(c_327,plain,
    ( sP0(k1_connsp_2(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

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

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | k6_setfam_1(u1_struct_0(X1),sK4(X0,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3024,plain,
    ( ~ sP0(X0_46,X0_48,X1_46)
    | k6_setfam_1(u1_struct_0(X0_48),sK4(X0_46,X0_48,X1_46)) = X0_46 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3427,plain,
    ( k6_setfam_1(u1_struct_0(X0_48),sK4(X0_46,X0_48,X1_46)) = X0_46
    | sP0(X0_46,X0_48,X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3024])).

cnf(c_3880,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = k1_connsp_2(sK5,X0_46)
    | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3437,c_3427])).

cnf(c_4231,plain,
    ( k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) = k1_connsp_2(sK5,sK6) ),
    inference(superposition,[status(thm)],[c_3434,c_3880])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3019,plain,
    ( ~ sP0(X0_46,X0_48,X1_46)
    | m1_subset_1(sK4(X0_46,X0_48,X1_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3432,plain,
    ( sP0(X0_46,X0_48,X1_46) != iProver_top
    | m1_subset_1(sK4(X0_46,X0_48,X1_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3019])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v4_pre_topc(sK2(X1,X0),X1)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v4_pre_topc(sK2(X1,X0),X1)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v4_pre_topc(sK2(sK5,X0),sK5)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_399,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ v4_pre_topc(sK2(sK5,X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_21])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v4_pre_topc(sK2(sK5,X0),sK5)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5) ),
    inference(renaming,[status(thm)],[c_399])).

cnf(c_3011,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ v4_pre_topc(sK2(sK5,X0_46),sK5)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) ),
    inference(subtyping,[status(esa)],[c_400])).

cnf(c_3440,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | v4_pre_topc(sK2(sK5,X0_46),sK5) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3011])).

cnf(c_3971,plain,
    ( sP0(X0_46,sK5,X1_46) != iProver_top
    | v4_pre_topc(sK2(sK5,sK4(X0_46,sK5,X1_46)),sK5) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(X0_46,sK5,X1_46)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_3440])).

cnf(c_4311,plain,
    ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
    | v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) = iProver_top
    | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4231,c_3971])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,sK4(X0,X1,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X3,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3021,plain,
    ( ~ sP0(X0_46,X0_48,X1_46)
    | ~ r2_hidden(X2_46,sK4(X0_46,X0_48,X1_46))
    | ~ m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(X0_48)))
    | v4_pre_topc(X2_46,X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4099,plain,
    ( ~ sP0(X0_46,sK5,X1_46)
    | ~ r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X2_46),sK5,X2_46)),sK4(X0_46,sK5,X1_46))
    | ~ m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X2_46),sK5,X2_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,X2_46),sK5,X2_46)),sK5) ),
    inference(instantiation,[status(thm)],[c_3021])).

cnf(c_4232,plain,
    ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | ~ r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46))
    | ~ m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5) ),
    inference(instantiation,[status(thm)],[c_4099])).

cnf(c_4233,plain,
    ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) != iProver_top
    | r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != iProver_top
    | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4232])).

cnf(c_4235,plain,
    ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
    | r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) != iProver_top
    | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4233])).

cnf(c_3034,plain,
    ( ~ v4_pre_topc(X0_46,X0_48)
    | v4_pre_topc(X1_46,X0_48)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_3788,plain,
    ( v4_pre_topc(X0_46,sK5)
    | ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5)
    | X0_46 != k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)) ),
    inference(instantiation,[status(thm)],[c_3034])).

cnf(c_4016,plain,
    ( v4_pre_topc(k1_connsp_2(sK5,X0_46),sK5)
    | ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5)
    | k1_connsp_2(sK5,X0_46) != k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)) ),
    inference(instantiation,[status(thm)],[c_3788])).

cnf(c_4017,plain,
    ( k1_connsp_2(sK5,X0_46) != k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46))
    | v4_pre_topc(k1_connsp_2(sK5,X0_46),sK5) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4016])).

cnf(c_4019,plain,
    ( k1_connsp_2(sK5,sK6) != k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6))
    | v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4017])).

cnf(c_3,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k1_connsp_2(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_308,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X4,u1_struct_0(sK5))
    | X4 != X2
    | X3 != X0
    | k1_connsp_2(X1,X2) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_285])).

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
    ( ~ sP0(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK5))
    | ~ m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | k1_connsp_2(sK5,X1_46) = k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) ),
    inference(instantiation,[status(thm)],[c_3015])).

cnf(c_3810,plain,
    ( ~ sP0(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5,sK6)
    | ~ m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | k1_connsp_2(sK5,sK6) = k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3808])).

cnf(c_3038,plain,
    ( ~ sP0(X0_46,X0_48,X1_46)
    | sP0(X2_46,X0_48,X1_46)
    | X2_46 != X0_46 ),
    theory(equality)).

cnf(c_3657,plain,
    ( sP0(X0_46,sK5,X1_46)
    | ~ sP0(k1_connsp_2(sK5,X1_46),sK5,X1_46)
    | X0_46 != k1_connsp_2(sK5,X1_46) ),
    inference(instantiation,[status(thm)],[c_3038])).

cnf(c_3748,plain,
    ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | sP0(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5,X0_46)
    | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != k1_connsp_2(sK5,X0_46) ),
    inference(instantiation,[status(thm)],[c_3657])).

cnf(c_3750,plain,
    ( ~ sP0(k1_connsp_2(sK5,sK6),sK5,sK6)
    | sP0(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5,sK6)
    | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) != k1_connsp_2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3748])).

cnf(c_3035,plain,
    ( ~ m1_subset_1(X0_46,X0_47)
    | m1_subset_1(X1_46,X0_47)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_3616,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k1_connsp_2(sK5,X1_46),k1_zfmisc_1(u1_struct_0(sK5)))
    | X0_46 != k1_connsp_2(sK5,X1_46) ),
    inference(instantiation,[status(thm)],[c_3035])).

cnf(c_3736,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK5,X0_46),k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != k1_connsp_2(sK5,X0_46) ),
    inference(instantiation,[status(thm)],[c_3616])).

cnf(c_3738,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) != k1_connsp_2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3736])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_352,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ v2_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_353,plain,
    ( r2_hidden(sK2(sK5,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_357,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | r2_hidden(sK2(sK5,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_21])).

cnf(c_358,plain,
    ( r2_hidden(sK2(sK5,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5) ),
    inference(renaming,[status(thm)],[c_357])).

cnf(c_3013,plain,
    ( r2_hidden(sK2(sK5,X0_46),X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) ),
    inference(subtyping,[status(esa)],[c_358])).

cnf(c_3696,plain,
    ( r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46))
    | ~ m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) ),
    inference(instantiation,[status(thm)],[c_3013])).

cnf(c_3702,plain,
    ( r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = iProver_top
    | m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3696])).

cnf(c_3704,plain,
    ( r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) = iProver_top
    | m1_subset_1(sK4(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3702])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_378,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
    | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_21])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5) ),
    inference(renaming,[status(thm)],[c_378])).

cnf(c_3012,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK2(sK5,X0_46),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_3697,plain,
    ( ~ m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) ),
    inference(instantiation,[status(thm)],[c_3012])).

cnf(c_3698,plain,
    ( m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3697])).

cnf(c_3700,plain,
    ( m1_subset_1(sK4(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3698])).

cnf(c_3630,plain,
    ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = k1_connsp_2(sK5,X0_46) ),
    inference(instantiation,[status(thm)],[c_3024])).

cnf(c_3632,plain,
    ( ~ sP0(k1_connsp_2(sK5,sK6),sK5,sK6)
    | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) = k1_connsp_2(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_3630])).

cnf(c_3625,plain,
    ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
    | m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_3019])).

cnf(c_3626,plain,
    ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) != iProver_top
    | m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3625])).

cnf(c_3628,plain,
    ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
    | m1_subset_1(sK4(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.87/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/0.98  
% 1.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/0.98  
% 1.87/0.98  ------  iProver source info
% 1.87/0.98  
% 1.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/0.98  git: non_committed_changes: false
% 1.87/0.98  git: last_make_outside_of_git: false
% 1.87/0.98  
% 1.87/0.98  ------ 
% 1.87/0.98  
% 1.87/0.98  ------ Input Options
% 1.87/0.98  
% 1.87/0.98  --out_options                           all
% 1.87/0.98  --tptp_safe_out                         true
% 1.87/0.98  --problem_path                          ""
% 1.87/0.98  --include_path                          ""
% 1.87/0.98  --clausifier                            res/vclausify_rel
% 1.87/0.98  --clausifier_options                    --mode clausify
% 1.87/0.98  --stdin                                 false
% 1.87/0.98  --stats_out                             all
% 1.87/0.98  
% 1.87/0.98  ------ General Options
% 1.87/0.98  
% 1.87/0.98  --fof                                   false
% 1.87/0.98  --time_out_real                         305.
% 1.87/0.98  --time_out_virtual                      -1.
% 1.87/0.98  --symbol_type_check                     false
% 1.87/0.98  --clausify_out                          false
% 1.87/0.98  --sig_cnt_out                           false
% 1.87/0.98  --trig_cnt_out                          false
% 1.87/0.98  --trig_cnt_out_tolerance                1.
% 1.87/0.98  --trig_cnt_out_sk_spl                   false
% 1.87/0.98  --abstr_cl_out                          false
% 1.87/0.98  
% 1.87/0.98  ------ Global Options
% 1.87/0.98  
% 1.87/0.98  --schedule                              default
% 1.87/0.98  --add_important_lit                     false
% 1.87/0.98  --prop_solver_per_cl                    1000
% 1.87/0.98  --min_unsat_core                        false
% 1.87/0.98  --soft_assumptions                      false
% 1.87/0.98  --soft_lemma_size                       3
% 1.87/0.98  --prop_impl_unit_size                   0
% 1.87/0.98  --prop_impl_unit                        []
% 1.87/0.98  --share_sel_clauses                     true
% 1.87/0.98  --reset_solvers                         false
% 1.87/0.98  --bc_imp_inh                            [conj_cone]
% 1.87/0.98  --conj_cone_tolerance                   3.
% 1.87/0.98  --extra_neg_conj                        none
% 1.87/0.98  --large_theory_mode                     true
% 1.87/0.98  --prolific_symb_bound                   200
% 1.87/0.98  --lt_threshold                          2000
% 1.87/0.98  --clause_weak_htbl                      true
% 1.87/0.98  --gc_record_bc_elim                     false
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing Options
% 1.87/0.98  
% 1.87/0.98  --preprocessing_flag                    true
% 1.87/0.98  --time_out_prep_mult                    0.1
% 1.87/0.98  --splitting_mode                        input
% 1.87/0.98  --splitting_grd                         true
% 1.87/0.98  --splitting_cvd                         false
% 1.87/0.98  --splitting_cvd_svl                     false
% 1.87/0.98  --splitting_nvd                         32
% 1.87/0.98  --sub_typing                            true
% 1.87/0.98  --prep_gs_sim                           true
% 1.87/0.98  --prep_unflatten                        true
% 1.87/0.98  --prep_res_sim                          true
% 1.87/0.98  --prep_upred                            true
% 1.87/0.98  --prep_sem_filter                       exhaustive
% 1.87/0.98  --prep_sem_filter_out                   false
% 1.87/0.98  --pred_elim                             true
% 1.87/0.98  --res_sim_input                         true
% 1.87/0.98  --eq_ax_congr_red                       true
% 1.87/0.98  --pure_diseq_elim                       true
% 1.87/0.98  --brand_transform                       false
% 1.87/0.98  --non_eq_to_eq                          false
% 1.87/0.98  --prep_def_merge                        true
% 1.87/0.98  --prep_def_merge_prop_impl              false
% 1.87/0.98  --prep_def_merge_mbd                    true
% 1.87/0.98  --prep_def_merge_tr_red                 false
% 1.87/0.98  --prep_def_merge_tr_cl                  false
% 1.87/0.98  --smt_preprocessing                     true
% 1.87/0.98  --smt_ac_axioms                         fast
% 1.87/0.98  --preprocessed_out                      false
% 1.87/0.98  --preprocessed_stats                    false
% 1.87/0.98  
% 1.87/0.98  ------ Abstraction refinement Options
% 1.87/0.98  
% 1.87/0.98  --abstr_ref                             []
% 1.87/0.98  --abstr_ref_prep                        false
% 1.87/0.98  --abstr_ref_until_sat                   false
% 1.87/0.98  --abstr_ref_sig_restrict                funpre
% 1.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.98  --abstr_ref_under                       []
% 1.87/0.98  
% 1.87/0.98  ------ SAT Options
% 1.87/0.98  
% 1.87/0.98  --sat_mode                              false
% 1.87/0.98  --sat_fm_restart_options                ""
% 1.87/0.98  --sat_gr_def                            false
% 1.87/0.98  --sat_epr_types                         true
% 1.87/0.98  --sat_non_cyclic_types                  false
% 1.87/0.98  --sat_finite_models                     false
% 1.87/0.98  --sat_fm_lemmas                         false
% 1.87/0.98  --sat_fm_prep                           false
% 1.87/0.98  --sat_fm_uc_incr                        true
% 1.87/0.98  --sat_out_model                         small
% 1.87/0.98  --sat_out_clauses                       false
% 1.87/0.98  
% 1.87/0.98  ------ QBF Options
% 1.87/0.98  
% 1.87/0.98  --qbf_mode                              false
% 1.87/0.98  --qbf_elim_univ                         false
% 1.87/0.98  --qbf_dom_inst                          none
% 1.87/0.98  --qbf_dom_pre_inst                      false
% 1.87/0.98  --qbf_sk_in                             false
% 1.87/0.98  --qbf_pred_elim                         true
% 1.87/0.98  --qbf_split                             512
% 1.87/0.98  
% 1.87/0.98  ------ BMC1 Options
% 1.87/0.98  
% 1.87/0.98  --bmc1_incremental                      false
% 1.87/0.98  --bmc1_axioms                           reachable_all
% 1.87/0.98  --bmc1_min_bound                        0
% 1.87/0.98  --bmc1_max_bound                        -1
% 1.87/0.98  --bmc1_max_bound_default                -1
% 1.87/0.98  --bmc1_symbol_reachability              true
% 1.87/0.98  --bmc1_property_lemmas                  false
% 1.87/0.98  --bmc1_k_induction                      false
% 1.87/0.98  --bmc1_non_equiv_states                 false
% 1.87/0.98  --bmc1_deadlock                         false
% 1.87/0.98  --bmc1_ucm                              false
% 1.87/0.98  --bmc1_add_unsat_core                   none
% 1.87/0.98  --bmc1_unsat_core_children              false
% 1.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.98  --bmc1_out_stat                         full
% 1.87/0.98  --bmc1_ground_init                      false
% 1.87/0.98  --bmc1_pre_inst_next_state              false
% 1.87/0.98  --bmc1_pre_inst_state                   false
% 1.87/0.98  --bmc1_pre_inst_reach_state             false
% 1.87/0.98  --bmc1_out_unsat_core                   false
% 1.87/0.98  --bmc1_aig_witness_out                  false
% 1.87/0.98  --bmc1_verbose                          false
% 1.87/0.98  --bmc1_dump_clauses_tptp                false
% 1.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.98  --bmc1_dump_file                        -
% 1.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.98  --bmc1_ucm_extend_mode                  1
% 1.87/0.98  --bmc1_ucm_init_mode                    2
% 1.87/0.98  --bmc1_ucm_cone_mode                    none
% 1.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.98  --bmc1_ucm_relax_model                  4
% 1.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.98  --bmc1_ucm_layered_model                none
% 1.87/0.98  --bmc1_ucm_max_lemma_size               10
% 1.87/0.98  
% 1.87/0.98  ------ AIG Options
% 1.87/0.98  
% 1.87/0.98  --aig_mode                              false
% 1.87/0.98  
% 1.87/0.98  ------ Instantiation Options
% 1.87/0.98  
% 1.87/0.98  --instantiation_flag                    true
% 1.87/0.98  --inst_sos_flag                         false
% 1.87/0.98  --inst_sos_phase                        true
% 1.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.98  --inst_lit_sel_side                     num_symb
% 1.87/0.98  --inst_solver_per_active                1400
% 1.87/0.98  --inst_solver_calls_frac                1.
% 1.87/0.98  --inst_passive_queue_type               priority_queues
% 1.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.98  --inst_passive_queues_freq              [25;2]
% 1.87/0.98  --inst_dismatching                      true
% 1.87/0.98  --inst_eager_unprocessed_to_passive     true
% 1.87/0.98  --inst_prop_sim_given                   true
% 1.87/0.98  --inst_prop_sim_new                     false
% 1.87/0.98  --inst_subs_new                         false
% 1.87/0.98  --inst_eq_res_simp                      false
% 1.87/0.98  --inst_subs_given                       false
% 1.87/0.98  --inst_orphan_elimination               true
% 1.87/0.98  --inst_learning_loop_flag               true
% 1.87/0.98  --inst_learning_start                   3000
% 1.87/0.98  --inst_learning_factor                  2
% 1.87/0.98  --inst_start_prop_sim_after_learn       3
% 1.87/0.98  --inst_sel_renew                        solver
% 1.87/0.98  --inst_lit_activity_flag                true
% 1.87/0.98  --inst_restr_to_given                   false
% 1.87/0.98  --inst_activity_threshold               500
% 1.87/0.98  --inst_out_proof                        true
% 1.87/0.98  
% 1.87/0.98  ------ Resolution Options
% 1.87/0.98  
% 1.87/0.98  --resolution_flag                       true
% 1.87/0.98  --res_lit_sel                           adaptive
% 1.87/0.98  --res_lit_sel_side                      none
% 1.87/0.98  --res_ordering                          kbo
% 1.87/0.98  --res_to_prop_solver                    active
% 1.87/0.98  --res_prop_simpl_new                    false
% 1.87/0.98  --res_prop_simpl_given                  true
% 1.87/0.98  --res_passive_queue_type                priority_queues
% 1.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.98  --res_passive_queues_freq               [15;5]
% 1.87/0.98  --res_forward_subs                      full
% 1.87/0.98  --res_backward_subs                     full
% 1.87/0.98  --res_forward_subs_resolution           true
% 1.87/0.98  --res_backward_subs_resolution          true
% 1.87/0.98  --res_orphan_elimination                true
% 1.87/0.98  --res_time_limit                        2.
% 1.87/0.98  --res_out_proof                         true
% 1.87/0.98  
% 1.87/0.98  ------ Superposition Options
% 1.87/0.98  
% 1.87/0.98  --superposition_flag                    true
% 1.87/0.98  --sup_passive_queue_type                priority_queues
% 1.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.98  --demod_completeness_check              fast
% 1.87/0.98  --demod_use_ground                      true
% 1.87/0.98  --sup_to_prop_solver                    passive
% 1.87/0.98  --sup_prop_simpl_new                    true
% 1.87/0.98  --sup_prop_simpl_given                  true
% 1.87/0.98  --sup_fun_splitting                     false
% 1.87/0.98  --sup_smt_interval                      50000
% 1.87/0.98  
% 1.87/0.98  ------ Superposition Simplification Setup
% 1.87/0.98  
% 1.87/0.98  --sup_indices_passive                   []
% 1.87/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.98  --sup_full_bw                           [BwDemod]
% 1.87/0.98  --sup_immed_triv                        [TrivRules]
% 1.87/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.98  --sup_immed_bw_main                     []
% 1.87/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.98  
% 1.87/0.98  ------ Combination Options
% 1.87/0.98  
% 1.87/0.98  --comb_res_mult                         3
% 1.87/0.98  --comb_sup_mult                         2
% 1.87/0.98  --comb_inst_mult                        10
% 1.87/0.98  
% 1.87/0.98  ------ Debug Options
% 1.87/0.98  
% 1.87/0.98  --dbg_backtrace                         false
% 1.87/0.98  --dbg_dump_prop_clauses                 false
% 1.87/0.98  --dbg_dump_prop_clauses_file            -
% 1.87/0.98  --dbg_out_stat                          false
% 1.87/0.98  ------ Parsing...
% 1.87/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/0.98  
% 1.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/0.98  ------ Proving...
% 1.87/0.98  ------ Problem Properties 
% 1.87/0.98  
% 1.87/0.98  
% 1.87/0.98  clauses                                 19
% 1.87/0.98  conjectures                             2
% 1.87/0.98  EPR                                     0
% 1.87/0.98  Horn                                    13
% 1.87/0.98  unary                                   2
% 1.87/0.98  binary                                  4
% 1.87/0.98  lits                                    62
% 1.87/0.98  lits eq                                 2
% 1.87/0.98  fd_pure                                 0
% 1.87/0.98  fd_pseudo                               0
% 1.87/0.98  fd_cond                                 0
% 1.87/0.98  fd_pseudo_cond                          1
% 1.87/0.98  AC symbols                              0
% 1.87/0.98  
% 1.87/0.98  ------ Schedule dynamic 5 is on 
% 1.87/0.98  
% 1.87/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.87/0.98  
% 1.87/0.98  
% 1.87/0.98  ------ 
% 1.87/0.98  Current options:
% 1.87/0.98  ------ 
% 1.87/0.98  
% 1.87/0.98  ------ Input Options
% 1.87/0.98  
% 1.87/0.98  --out_options                           all
% 1.87/0.98  --tptp_safe_out                         true
% 1.87/0.98  --problem_path                          ""
% 1.87/0.98  --include_path                          ""
% 1.87/0.98  --clausifier                            res/vclausify_rel
% 1.87/0.98  --clausifier_options                    --mode clausify
% 1.87/0.98  --stdin                                 false
% 1.87/0.98  --stats_out                             all
% 1.87/0.99  
% 1.87/0.99  ------ General Options
% 1.87/0.99  
% 1.87/0.99  --fof                                   false
% 1.87/0.99  --time_out_real                         305.
% 1.87/0.99  --time_out_virtual                      -1.
% 1.87/0.99  --symbol_type_check                     false
% 1.87/0.99  --clausify_out                          false
% 1.87/0.99  --sig_cnt_out                           false
% 1.87/0.99  --trig_cnt_out                          false
% 1.87/0.99  --trig_cnt_out_tolerance                1.
% 1.87/0.99  --trig_cnt_out_sk_spl                   false
% 1.87/0.99  --abstr_cl_out                          false
% 1.87/0.99  
% 1.87/0.99  ------ Global Options
% 1.87/0.99  
% 1.87/0.99  --schedule                              default
% 1.87/0.99  --add_important_lit                     false
% 1.87/0.99  --prop_solver_per_cl                    1000
% 1.87/0.99  --min_unsat_core                        false
% 1.87/0.99  --soft_assumptions                      false
% 1.87/0.99  --soft_lemma_size                       3
% 1.87/0.99  --prop_impl_unit_size                   0
% 1.87/0.99  --prop_impl_unit                        []
% 1.87/0.99  --share_sel_clauses                     true
% 1.87/0.99  --reset_solvers                         false
% 1.87/0.99  --bc_imp_inh                            [conj_cone]
% 1.87/0.99  --conj_cone_tolerance                   3.
% 1.87/0.99  --extra_neg_conj                        none
% 1.87/0.99  --large_theory_mode                     true
% 1.87/0.99  --prolific_symb_bound                   200
% 1.87/0.99  --lt_threshold                          2000
% 1.87/0.99  --clause_weak_htbl                      true
% 1.87/0.99  --gc_record_bc_elim                     false
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing Options
% 1.87/0.99  
% 1.87/0.99  --preprocessing_flag                    true
% 1.87/0.99  --time_out_prep_mult                    0.1
% 1.87/0.99  --splitting_mode                        input
% 1.87/0.99  --splitting_grd                         true
% 1.87/0.99  --splitting_cvd                         false
% 1.87/0.99  --splitting_cvd_svl                     false
% 1.87/0.99  --splitting_nvd                         32
% 1.87/0.99  --sub_typing                            true
% 1.87/0.99  --prep_gs_sim                           true
% 1.87/0.99  --prep_unflatten                        true
% 1.87/0.99  --prep_res_sim                          true
% 1.87/0.99  --prep_upred                            true
% 1.87/0.99  --prep_sem_filter                       exhaustive
% 1.87/0.99  --prep_sem_filter_out                   false
% 1.87/0.99  --pred_elim                             true
% 1.87/0.99  --res_sim_input                         true
% 1.87/0.99  --eq_ax_congr_red                       true
% 1.87/0.99  --pure_diseq_elim                       true
% 1.87/0.99  --brand_transform                       false
% 1.87/0.99  --non_eq_to_eq                          false
% 1.87/0.99  --prep_def_merge                        true
% 1.87/0.99  --prep_def_merge_prop_impl              false
% 1.87/0.99  --prep_def_merge_mbd                    true
% 1.87/0.99  --prep_def_merge_tr_red                 false
% 1.87/0.99  --prep_def_merge_tr_cl                  false
% 1.87/0.99  --smt_preprocessing                     true
% 1.87/0.99  --smt_ac_axioms                         fast
% 1.87/0.99  --preprocessed_out                      false
% 1.87/0.99  --preprocessed_stats                    false
% 1.87/0.99  
% 1.87/0.99  ------ Abstraction refinement Options
% 1.87/0.99  
% 1.87/0.99  --abstr_ref                             []
% 1.87/0.99  --abstr_ref_prep                        false
% 1.87/0.99  --abstr_ref_until_sat                   false
% 1.87/0.99  --abstr_ref_sig_restrict                funpre
% 1.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.99  --abstr_ref_under                       []
% 1.87/0.99  
% 1.87/0.99  ------ SAT Options
% 1.87/0.99  
% 1.87/0.99  --sat_mode                              false
% 1.87/0.99  --sat_fm_restart_options                ""
% 1.87/0.99  --sat_gr_def                            false
% 1.87/0.99  --sat_epr_types                         true
% 1.87/0.99  --sat_non_cyclic_types                  false
% 1.87/0.99  --sat_finite_models                     false
% 1.87/0.99  --sat_fm_lemmas                         false
% 1.87/0.99  --sat_fm_prep                           false
% 1.87/0.99  --sat_fm_uc_incr                        true
% 1.87/0.99  --sat_out_model                         small
% 1.87/0.99  --sat_out_clauses                       false
% 1.87/0.99  
% 1.87/0.99  ------ QBF Options
% 1.87/0.99  
% 1.87/0.99  --qbf_mode                              false
% 1.87/0.99  --qbf_elim_univ                         false
% 1.87/0.99  --qbf_dom_inst                          none
% 1.87/0.99  --qbf_dom_pre_inst                      false
% 1.87/0.99  --qbf_sk_in                             false
% 1.87/0.99  --qbf_pred_elim                         true
% 1.87/0.99  --qbf_split                             512
% 1.87/0.99  
% 1.87/0.99  ------ BMC1 Options
% 1.87/0.99  
% 1.87/0.99  --bmc1_incremental                      false
% 1.87/0.99  --bmc1_axioms                           reachable_all
% 1.87/0.99  --bmc1_min_bound                        0
% 1.87/0.99  --bmc1_max_bound                        -1
% 1.87/0.99  --bmc1_max_bound_default                -1
% 1.87/0.99  --bmc1_symbol_reachability              true
% 1.87/0.99  --bmc1_property_lemmas                  false
% 1.87/0.99  --bmc1_k_induction                      false
% 1.87/0.99  --bmc1_non_equiv_states                 false
% 1.87/0.99  --bmc1_deadlock                         false
% 1.87/0.99  --bmc1_ucm                              false
% 1.87/0.99  --bmc1_add_unsat_core                   none
% 1.87/0.99  --bmc1_unsat_core_children              false
% 1.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.99  --bmc1_out_stat                         full
% 1.87/0.99  --bmc1_ground_init                      false
% 1.87/0.99  --bmc1_pre_inst_next_state              false
% 1.87/0.99  --bmc1_pre_inst_state                   false
% 1.87/0.99  --bmc1_pre_inst_reach_state             false
% 1.87/0.99  --bmc1_out_unsat_core                   false
% 1.87/0.99  --bmc1_aig_witness_out                  false
% 1.87/0.99  --bmc1_verbose                          false
% 1.87/0.99  --bmc1_dump_clauses_tptp                false
% 1.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.99  --bmc1_dump_file                        -
% 1.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.99  --bmc1_ucm_extend_mode                  1
% 1.87/0.99  --bmc1_ucm_init_mode                    2
% 1.87/0.99  --bmc1_ucm_cone_mode                    none
% 1.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.99  --bmc1_ucm_relax_model                  4
% 1.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.99  --bmc1_ucm_layered_model                none
% 1.87/0.99  --bmc1_ucm_max_lemma_size               10
% 1.87/0.99  
% 1.87/0.99  ------ AIG Options
% 1.87/0.99  
% 1.87/0.99  --aig_mode                              false
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation Options
% 1.87/0.99  
% 1.87/0.99  --instantiation_flag                    true
% 1.87/0.99  --inst_sos_flag                         false
% 1.87/0.99  --inst_sos_phase                        true
% 1.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel_side                     none
% 1.87/0.99  --inst_solver_per_active                1400
% 1.87/0.99  --inst_solver_calls_frac                1.
% 1.87/0.99  --inst_passive_queue_type               priority_queues
% 1.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.99  --inst_passive_queues_freq              [25;2]
% 1.87/0.99  --inst_dismatching                      true
% 1.87/0.99  --inst_eager_unprocessed_to_passive     true
% 1.87/0.99  --inst_prop_sim_given                   true
% 1.87/0.99  --inst_prop_sim_new                     false
% 1.87/0.99  --inst_subs_new                         false
% 1.87/0.99  --inst_eq_res_simp                      false
% 1.87/0.99  --inst_subs_given                       false
% 1.87/0.99  --inst_orphan_elimination               true
% 1.87/0.99  --inst_learning_loop_flag               true
% 1.87/0.99  --inst_learning_start                   3000
% 1.87/0.99  --inst_learning_factor                  2
% 1.87/0.99  --inst_start_prop_sim_after_learn       3
% 1.87/0.99  --inst_sel_renew                        solver
% 1.87/0.99  --inst_lit_activity_flag                true
% 1.87/0.99  --inst_restr_to_given                   false
% 1.87/0.99  --inst_activity_threshold               500
% 1.87/0.99  --inst_out_proof                        true
% 1.87/0.99  
% 1.87/0.99  ------ Resolution Options
% 1.87/0.99  
% 1.87/0.99  --resolution_flag                       false
% 1.87/0.99  --res_lit_sel                           adaptive
% 1.87/0.99  --res_lit_sel_side                      none
% 1.87/0.99  --res_ordering                          kbo
% 1.87/0.99  --res_to_prop_solver                    active
% 1.87/0.99  --res_prop_simpl_new                    false
% 1.87/0.99  --res_prop_simpl_given                  true
% 1.87/0.99  --res_passive_queue_type                priority_queues
% 1.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.99  --res_passive_queues_freq               [15;5]
% 1.87/0.99  --res_forward_subs                      full
% 1.87/0.99  --res_backward_subs                     full
% 1.87/0.99  --res_forward_subs_resolution           true
% 1.87/0.99  --res_backward_subs_resolution          true
% 1.87/0.99  --res_orphan_elimination                true
% 1.87/0.99  --res_time_limit                        2.
% 1.87/0.99  --res_out_proof                         true
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Options
% 1.87/0.99  
% 1.87/0.99  --superposition_flag                    true
% 1.87/0.99  --sup_passive_queue_type                priority_queues
% 1.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.99  --demod_completeness_check              fast
% 1.87/0.99  --demod_use_ground                      true
% 1.87/0.99  --sup_to_prop_solver                    passive
% 1.87/0.99  --sup_prop_simpl_new                    true
% 1.87/0.99  --sup_prop_simpl_given                  true
% 1.87/0.99  --sup_fun_splitting                     false
% 1.87/0.99  --sup_smt_interval                      50000
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Simplification Setup
% 1.87/0.99  
% 1.87/0.99  --sup_indices_passive                   []
% 1.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_full_bw                           [BwDemod]
% 1.87/0.99  --sup_immed_triv                        [TrivRules]
% 1.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_immed_bw_main                     []
% 1.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  
% 1.87/0.99  ------ Combination Options
% 1.87/0.99  
% 1.87/0.99  --comb_res_mult                         3
% 1.87/0.99  --comb_sup_mult                         2
% 1.87/0.99  --comb_inst_mult                        10
% 1.87/0.99  
% 1.87/0.99  ------ Debug Options
% 1.87/0.99  
% 1.87/0.99  --dbg_backtrace                         false
% 1.87/0.99  --dbg_dump_prop_clauses                 false
% 1.87/0.99  --dbg_dump_prop_clauses_file            -
% 1.87/0.99  --dbg_out_stat                          false
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  ------ Proving...
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS status Theorem for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  fof(f4,conjecture,(
% 1.87/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v4_pre_topc(k1_connsp_2(X0,X1),X0)))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f5,negated_conjecture,(
% 1.87/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v4_pre_topc(k1_connsp_2(X0,X1),X0)))),
% 1.87/0.99    inference(negated_conjecture,[],[f4])).
% 1.87/0.99  
% 1.87/0.99  fof(f12,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (~v4_pre_topc(k1_connsp_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f5])).
% 1.87/0.99  
% 1.87/0.99  fof(f13,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (~v4_pre_topc(k1_connsp_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f12])).
% 1.87/0.99  
% 1.87/0.99  fof(f28,plain,(
% 1.87/0.99    ( ! [X0] : (? [X1] : (~v4_pre_topc(k1_connsp_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v4_pre_topc(k1_connsp_2(X0,sK6),X0) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f27,plain,(
% 1.87/0.99    ? [X0] : (? [X1] : (~v4_pre_topc(k1_connsp_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v4_pre_topc(k1_connsp_2(sK5,X1),sK5) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f29,plain,(
% 1.87/0.99    (~v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f28,f27])).
% 1.87/0.99  
% 1.87/0.99  fof(f51,plain,(
% 1.87/0.99    m1_subset_1(sK6,u1_struct_0(sK5))),
% 1.87/0.99    inference(cnf_transformation,[],[f29])).
% 1.87/0.99  
% 1.87/0.99  fof(f15,plain,(
% 1.87/0.99    ! [X1,X0,X2] : ((k1_connsp_2(X0,X1) = X2 <=> sP0(X2,X0,X1)) | ~sP1(X1,X0,X2))),
% 1.87/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.87/0.99  
% 1.87/0.99  fof(f19,plain,(
% 1.87/0.99    ! [X1,X0,X2] : (((k1_connsp_2(X0,X1) = X2 | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | k1_connsp_2(X0,X1) != X2)) | ~sP1(X1,X0,X2))),
% 1.87/0.99    inference(nnf_transformation,[],[f15])).
% 1.87/0.99  
% 1.87/0.99  fof(f20,plain,(
% 1.87/0.99    ! [X0,X1,X2] : (((k1_connsp_2(X1,X0) = X2 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k1_connsp_2(X1,X0) != X2)) | ~sP1(X0,X1,X2))),
% 1.87/0.99    inference(rectify,[],[f19])).
% 1.87/0.99  
% 1.87/0.99  fof(f33,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k1_connsp_2(X1,X0) != X2 | ~sP1(X0,X1,X2)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f20])).
% 1.87/0.99  
% 1.87/0.99  fof(f53,plain,(
% 1.87/0.99    ( ! [X0,X1] : (sP0(k1_connsp_2(X1,X0),X1,X0) | ~sP1(X0,X1,k1_connsp_2(X1,X0))) )),
% 1.87/0.99    inference(equality_resolution,[],[f33])).
% 1.87/0.99  
% 1.87/0.99  fof(f2,axiom,(
% 1.87/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f8,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f2])).
% 1.87/0.99  
% 1.87/0.99  fof(f9,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f8])).
% 1.87/0.99  
% 1.87/0.99  fof(f14,plain,(
% 1.87/0.99    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.87/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.87/0.99  
% 1.87/0.99  fof(f16,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(definition_folding,[],[f9,f15,f14])).
% 1.87/0.99  
% 1.87/0.99  fof(f46,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f16])).
% 1.87/0.99  
% 1.87/0.99  fof(f48,plain,(
% 1.87/0.99    ~v2_struct_0(sK5)),
% 1.87/0.99    inference(cnf_transformation,[],[f29])).
% 1.87/0.99  
% 1.87/0.99  fof(f49,plain,(
% 1.87/0.99    v2_pre_topc(sK5)),
% 1.87/0.99    inference(cnf_transformation,[],[f29])).
% 1.87/0.99  
% 1.87/0.99  fof(f50,plain,(
% 1.87/0.99    l1_pre_topc(sK5)),
% 1.87/0.99    inference(cnf_transformation,[],[f29])).
% 1.87/0.99  
% 1.87/0.99  fof(f3,axiom,(
% 1.87/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f10,plain,(
% 1.87/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f3])).
% 1.87/0.99  
% 1.87/0.99  fof(f11,plain,(
% 1.87/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.87/0.99    inference(flattening,[],[f10])).
% 1.87/0.99  
% 1.87/0.99  fof(f47,plain,(
% 1.87/0.99    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f11])).
% 1.87/0.99  
% 1.87/0.99  fof(f21,plain,(
% 1.87/0.99    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ! [X3] : (k6_setfam_1(u1_struct_0(X0),X3) != X2 | ? [X4] : ((((~r2_hidden(X1,X4) | ~v4_pre_topc(X4,X0) | ~v3_pre_topc(X4,X0)) | ~r2_hidden(X4,X3)) & ((r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0)) | r2_hidden(X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : (((r2_hidden(X4,X3) | (~r2_hidden(X1,X4) | ~v4_pre_topc(X4,X0) | ~v3_pre_topc(X4,X0))) & ((r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0)) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~sP0(X2,X0,X1)))),
% 1.87/0.99    inference(nnf_transformation,[],[f14])).
% 1.87/0.99  
% 1.87/0.99  fof(f22,plain,(
% 1.87/0.99    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ! [X3] : (k6_setfam_1(u1_struct_0(X0),X3) != X2 | ? [X4] : ((~r2_hidden(X1,X4) | ~v4_pre_topc(X4,X0) | ~v3_pre_topc(X4,X0) | ~r2_hidden(X4,X3)) & ((r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0)) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : (((r2_hidden(X4,X3) | ~r2_hidden(X1,X4) | ~v4_pre_topc(X4,X0) | ~v3_pre_topc(X4,X0)) & ((r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0)) | ~r2_hidden(X4,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~sP0(X2,X0,X1)))),
% 1.87/0.99    inference(flattening,[],[f21])).
% 1.87/0.99  
% 1.87/0.99  fof(f23,plain,(
% 1.87/0.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k6_setfam_1(u1_struct_0(X1),X3) != X0 | ? [X4] : ((~r2_hidden(X2,X4) | ~v4_pre_topc(X4,X1) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X4,X3)) & ((r2_hidden(X2,X4) & v4_pre_topc(X4,X1) & v3_pre_topc(X4,X1)) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))) & (? [X5] : (k6_setfam_1(u1_struct_0(X1),X5) = X0 & ! [X6] : (((r2_hidden(X6,X5) | ~r2_hidden(X2,X6) | ~v4_pre_topc(X6,X1) | ~v3_pre_topc(X6,X1)) & ((r2_hidden(X2,X6) & v4_pre_topc(X6,X1) & v3_pre_topc(X6,X1)) | ~r2_hidden(X6,X5))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~sP0(X0,X1,X2)))),
% 1.87/0.99    inference(rectify,[],[f22])).
% 1.87/0.99  
% 1.87/0.99  fof(f25,plain,(
% 1.87/0.99    ! [X2,X1,X0] : (? [X5] : (k6_setfam_1(u1_struct_0(X1),X5) = X0 & ! [X6] : (((r2_hidden(X6,X5) | ~r2_hidden(X2,X6) | ~v4_pre_topc(X6,X1) | ~v3_pre_topc(X6,X1)) & ((r2_hidden(X2,X6) & v4_pre_topc(X6,X1) & v3_pre_topc(X6,X1)) | ~r2_hidden(X6,X5))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) => (k6_setfam_1(u1_struct_0(X1),sK4(X0,X1,X2)) = X0 & ! [X6] : (((r2_hidden(X6,sK4(X0,X1,X2)) | ~r2_hidden(X2,X6) | ~v4_pre_topc(X6,X1) | ~v3_pre_topc(X6,X1)) & ((r2_hidden(X2,X6) & v4_pre_topc(X6,X1) & v3_pre_topc(X6,X1)) | ~r2_hidden(X6,sK4(X0,X1,X2)))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f24,plain,(
% 1.87/0.99    ! [X3,X2,X1] : (? [X4] : ((~r2_hidden(X2,X4) | ~v4_pre_topc(X4,X1) | ~v3_pre_topc(X4,X1) | ~r2_hidden(X4,X3)) & ((r2_hidden(X2,X4) & v4_pre_topc(X4,X1) & v3_pre_topc(X4,X1)) | r2_hidden(X4,X3)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => ((~r2_hidden(X2,sK3(X1,X2,X3)) | ~v4_pre_topc(sK3(X1,X2,X3),X1) | ~v3_pre_topc(sK3(X1,X2,X3),X1) | ~r2_hidden(sK3(X1,X2,X3),X3)) & ((r2_hidden(X2,sK3(X1,X2,X3)) & v4_pre_topc(sK3(X1,X2,X3),X1) & v3_pre_topc(sK3(X1,X2,X3),X1)) | r2_hidden(sK3(X1,X2,X3),X3)) & m1_subset_1(sK3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f26,plain,(
% 1.87/0.99    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k6_setfam_1(u1_struct_0(X1),X3) != X0 | ((~r2_hidden(X2,sK3(X1,X2,X3)) | ~v4_pre_topc(sK3(X1,X2,X3),X1) | ~v3_pre_topc(sK3(X1,X2,X3),X1) | ~r2_hidden(sK3(X1,X2,X3),X3)) & ((r2_hidden(X2,sK3(X1,X2,X3)) & v4_pre_topc(sK3(X1,X2,X3),X1) & v3_pre_topc(sK3(X1,X2,X3),X1)) | r2_hidden(sK3(X1,X2,X3),X3)) & m1_subset_1(sK3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))) & ((k6_setfam_1(u1_struct_0(X1),sK4(X0,X1,X2)) = X0 & ! [X6] : (((r2_hidden(X6,sK4(X0,X1,X2)) | ~r2_hidden(X2,X6) | ~v4_pre_topc(X6,X1) | ~v3_pre_topc(X6,X1)) & ((r2_hidden(X2,X6) & v4_pre_topc(X6,X1) & v3_pre_topc(X6,X1)) | ~r2_hidden(X6,sK4(X0,X1,X2)))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~sP0(X0,X1,X2)))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).
% 1.87/0.99  
% 1.87/0.99  fof(f40,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (k6_setfam_1(u1_struct_0(X1),sK4(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f26])).
% 1.87/0.99  
% 1.87/0.99  fof(f35,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1,X2)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f26])).
% 1.87/0.99  
% 1.87/0.99  fof(f1,axiom,(
% 1.87/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))) => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f6,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : ((~v4_pre_topc(X2,X0) & r2_hidden(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f1])).
% 1.87/0.99  
% 1.87/0.99  fof(f7,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/0.99    inference(flattening,[],[f6])).
% 1.87/0.99  
% 1.87/0.99  fof(f17,plain,(
% 1.87/0.99    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f18,plain,(
% 1.87/0.99    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | (~v4_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f17])).
% 1.87/0.99  
% 1.87/0.99  fof(f32,plain,(
% 1.87/0.99    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f18])).
% 1.87/0.99  
% 1.87/0.99  fof(f37,plain,(
% 1.87/0.99    ( ! [X6,X2,X0,X1] : (v4_pre_topc(X6,X1) | ~r2_hidden(X6,sK4(X0,X1,X2)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1,X2)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f26])).
% 1.87/0.99  
% 1.87/0.99  fof(f34,plain,(
% 1.87/0.99    ( ! [X2,X0,X1] : (k1_connsp_2(X1,X0) = X2 | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f20])).
% 1.87/0.99  
% 1.87/0.99  fof(f31,plain,(
% 1.87/0.99    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f18])).
% 1.87/0.99  
% 1.87/0.99  fof(f30,plain,(
% 1.87/0.99    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f18])).
% 1.87/0.99  
% 1.87/0.99  fof(f52,plain,(
% 1.87/0.99    ~v4_pre_topc(k1_connsp_2(sK5,sK6),sK5)),
% 1.87/0.99    inference(cnf_transformation,[],[f29])).
% 1.87/0.99  
% 1.87/0.99  cnf(c_19,negated_conjecture,
% 1.87/0.99      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.87/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3017,negated_conjecture,
% 1.87/0.99      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3434,plain,
% 1.87/0.99      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3017]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4,plain,
% 1.87/0.99      ( ~ sP1(X0,X1,k1_connsp_2(X1,X0)) | sP0(k1_connsp_2(X1,X0),X1,X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_16,plain,
% 1.87/0.99      ( sP1(X0,X1,X2)
% 1.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v2_pre_topc(X1)
% 1.87/0.99      | ~ l1_pre_topc(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_22,negated_conjecture,
% 1.87/0.99      ( ~ v2_struct_0(sK5) ),
% 1.87/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_280,plain,
% 1.87/0.99      ( sP1(X0,X1,X2)
% 1.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.87/0.99      | ~ v2_pre_topc(X1)
% 1.87/0.99      | ~ l1_pre_topc(X1)
% 1.87/0.99      | sK5 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_281,plain,
% 1.87/0.99      ( sP1(X0,sK5,X1)
% 1.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.87/0.99      | ~ v2_pre_topc(sK5)
% 1.87/0.99      | ~ l1_pre_topc(sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_21,negated_conjecture,
% 1.87/0.99      ( v2_pre_topc(sK5) ),
% 1.87/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_20,negated_conjecture,
% 1.87/0.99      ( l1_pre_topc(sK5) ),
% 1.87/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_285,plain,
% 1.87/0.99      ( sP1(X0,sK5,X1)
% 1.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_281,c_21,c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_326,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(X0,X1),X0,X1)
% 1.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK5))
% 1.87/0.99      | X3 != X1
% 1.87/0.99      | k1_connsp_2(X0,X1) != X2
% 1.87/0.99      | sK5 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_285]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_327,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,X0),sK5,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.87/0.99      | ~ m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_326]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_17,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.87/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v2_struct_0(X1)
% 1.87/0.99      | ~ v2_pre_topc(X1)
% 1.87/0.99      | ~ l1_pre_topc(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_262,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.87/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | ~ v2_pre_topc(X1)
% 1.87/0.99      | ~ l1_pre_topc(X1)
% 1.87/0.99      | sK5 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_263,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.87/0.99      | m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ v2_pre_topc(sK5)
% 1.87/0.99      | ~ l1_pre_topc(sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_262]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_267,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.87/0.99      | m1_subset_1(k1_connsp_2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_263,c_21,c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_331,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.87/0.99      | sP0(k1_connsp_2(sK5,X0),sK5,X0) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_327,c_21,c_20,c_263]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_332,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,X0),sK5,X0)
% 1.87/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_331]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3014,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
% 1.87/0.99      | ~ m1_subset_1(X0_46,u1_struct_0(sK5)) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_332]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3437,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3014]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_10,plain,
% 1.87/0.99      ( ~ sP0(X0,X1,X2)
% 1.87/0.99      | k6_setfam_1(u1_struct_0(X1),sK4(X0,X1,X2)) = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3024,plain,
% 1.87/0.99      ( ~ sP0(X0_46,X0_48,X1_46)
% 1.87/0.99      | k6_setfam_1(u1_struct_0(X0_48),sK4(X0_46,X0_48,X1_46)) = X0_46 ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3427,plain,
% 1.87/0.99      ( k6_setfam_1(u1_struct_0(X0_48),sK4(X0_46,X0_48,X1_46)) = X0_46
% 1.87/0.99      | sP0(X0_46,X0_48,X1_46) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3024]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3880,plain,
% 1.87/0.99      ( k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = k1_connsp_2(sK5,X0_46)
% 1.87/0.99      | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_3437,c_3427]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4231,plain,
% 1.87/0.99      ( k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) = k1_connsp_2(sK5,sK6) ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_3434,c_3880]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_15,plain,
% 1.87/0.99      ( ~ sP0(X0,X1,X2)
% 1.87/0.99      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
% 1.87/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3019,plain,
% 1.87/0.99      ( ~ sP0(X0_46,X0_48,X1_46)
% 1.87/0.99      | m1_subset_1(sK4(X0_46,X0_48,X1_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3432,plain,
% 1.87/0.99      ( sP0(X0_46,X0_48,X1_46) != iProver_top
% 1.87/0.99      | m1_subset_1(sK4(X0_46,X0_48,X1_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3019]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_0,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.87/0.99      | ~ v4_pre_topc(sK2(X1,X0),X1)
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
% 1.87/0.99      | ~ v2_pre_topc(X1)
% 1.87/0.99      | ~ l1_pre_topc(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_394,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.87/0.99      | ~ v4_pre_topc(sK2(X1,X0),X1)
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
% 1.87/0.99      | ~ v2_pre_topc(X1)
% 1.87/0.99      | sK5 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_395,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | ~ v4_pre_topc(sK2(sK5,X0),sK5)
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
% 1.87/0.99      | ~ v2_pre_topc(sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_394]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_399,plain,
% 1.87/0.99      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
% 1.87/0.99      | ~ v4_pre_topc(sK2(sK5,X0),sK5)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_395,c_21]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_400,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | ~ v4_pre_topc(sK2(sK5,X0),sK5)
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_399]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3011,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | ~ v4_pre_topc(sK2(sK5,X0_46),sK5)
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_400]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3440,plain,
% 1.87/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 1.87/0.99      | v4_pre_topc(sK2(sK5,X0_46),sK5) != iProver_top
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3011]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3971,plain,
% 1.87/0.99      ( sP0(X0_46,sK5,X1_46) != iProver_top
% 1.87/0.99      | v4_pre_topc(sK2(sK5,sK4(X0_46,sK5,X1_46)),sK5) != iProver_top
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(X0_46,sK5,X1_46)),sK5) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_3432,c_3440]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4311,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
% 1.87/0.99      | v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) = iProver_top
% 1.87/0.99      | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_4231,c_3971]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_13,plain,
% 1.87/0.99      ( ~ sP0(X0,X1,X2)
% 1.87/0.99      | ~ r2_hidden(X3,sK4(X0,X1,X2))
% 1.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v4_pre_topc(X3,X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3021,plain,
% 1.87/0.99      ( ~ sP0(X0_46,X0_48,X1_46)
% 1.87/0.99      | ~ r2_hidden(X2_46,sK4(X0_46,X0_48,X1_46))
% 1.87/0.99      | ~ m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(X0_48)))
% 1.87/0.99      | v4_pre_topc(X2_46,X0_48) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4099,plain,
% 1.87/0.99      ( ~ sP0(X0_46,sK5,X1_46)
% 1.87/0.99      | ~ r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X2_46),sK5,X2_46)),sK4(X0_46,sK5,X1_46))
% 1.87/0.99      | ~ m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X2_46),sK5,X2_46)),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,X2_46),sK5,X2_46)),sK5) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3021]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4232,plain,
% 1.87/0.99      ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
% 1.87/0.99      | ~ r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46))
% 1.87/0.99      | ~ m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_4099]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4233,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) != iProver_top
% 1.87/0.99      | r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != iProver_top
% 1.87/0.99      | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 1.87/0.99      | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4232]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4235,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
% 1.87/0.99      | r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) != iProver_top
% 1.87/0.99      | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 1.87/0.99      | v4_pre_topc(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_4233]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3034,plain,
% 1.87/0.99      ( ~ v4_pre_topc(X0_46,X0_48)
% 1.87/0.99      | v4_pre_topc(X1_46,X0_48)
% 1.87/0.99      | X1_46 != X0_46 ),
% 1.87/0.99      theory(equality) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3788,plain,
% 1.87/0.99      ( v4_pre_topc(X0_46,sK5)
% 1.87/0.99      | ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5)
% 1.87/0.99      | X0_46 != k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3034]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4016,plain,
% 1.87/0.99      ( v4_pre_topc(k1_connsp_2(sK5,X0_46),sK5)
% 1.87/0.99      | ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5)
% 1.87/0.99      | k1_connsp_2(sK5,X0_46) != k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3788]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4017,plain,
% 1.87/0.99      ( k1_connsp_2(sK5,X0_46) != k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46))
% 1.87/0.99      | v4_pre_topc(k1_connsp_2(sK5,X0_46),sK5) = iProver_top
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X1_46),sK5,X1_46)),sK5) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4016]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4019,plain,
% 1.87/0.99      ( k1_connsp_2(sK5,sK6) != k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6))
% 1.87/0.99      | v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) = iProver_top
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) != iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_4017]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3,plain,
% 1.87/0.99      ( ~ sP1(X0,X1,X2) | ~ sP0(X2,X1,X0) | k1_connsp_2(X1,X0) = X2 ),
% 1.87/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_308,plain,
% 1.87/0.99      ( ~ sP0(X0,X1,X2)
% 1.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK5))
% 1.87/0.99      | X4 != X2
% 1.87/0.99      | X3 != X0
% 1.87/0.99      | k1_connsp_2(X1,X2) = X0
% 1.87/0.99      | sK5 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_285]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_309,plain,
% 1.87/0.99      ( ~ sP0(X0,sK5,X1)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.87/0.99      | k1_connsp_2(sK5,X1) = X0 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3015,plain,
% 1.87/0.99      ( ~ sP0(X0_46,sK5,X1_46)
% 1.87/0.99      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK5))
% 1.87/0.99      | k1_connsp_2(sK5,X1_46) = X0_46 ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_309]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3808,plain,
% 1.87/0.99      ( ~ sP0(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5,X1_46)
% 1.87/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK5))
% 1.87/0.99      | ~ m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | k1_connsp_2(sK5,X1_46) = k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3015]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3810,plain,
% 1.87/0.99      ( ~ sP0(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5,sK6)
% 1.87/0.99      | ~ m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 1.87/0.99      | k1_connsp_2(sK5,sK6) = k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3808]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3038,plain,
% 1.87/0.99      ( ~ sP0(X0_46,X0_48,X1_46)
% 1.87/0.99      | sP0(X2_46,X0_48,X1_46)
% 1.87/0.99      | X2_46 != X0_46 ),
% 1.87/0.99      theory(equality) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3657,plain,
% 1.87/0.99      ( sP0(X0_46,sK5,X1_46)
% 1.87/0.99      | ~ sP0(k1_connsp_2(sK5,X1_46),sK5,X1_46)
% 1.87/0.99      | X0_46 != k1_connsp_2(sK5,X1_46) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3038]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3748,plain,
% 1.87/0.99      ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
% 1.87/0.99      | sP0(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5,X0_46)
% 1.87/0.99      | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != k1_connsp_2(sK5,X0_46) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3657]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3750,plain,
% 1.87/0.99      ( ~ sP0(k1_connsp_2(sK5,sK6),sK5,sK6)
% 1.87/0.99      | sP0(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5,sK6)
% 1.87/0.99      | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) != k1_connsp_2(sK5,sK6) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3748]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3035,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_46,X0_47)
% 1.87/0.99      | m1_subset_1(X1_46,X0_47)
% 1.87/0.99      | X1_46 != X0_46 ),
% 1.87/0.99      theory(equality) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3616,plain,
% 1.87/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(k1_connsp_2(sK5,X1_46),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | X0_46 != k1_connsp_2(sK5,X1_46) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3035]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3736,plain,
% 1.87/0.99      ( ~ m1_subset_1(k1_connsp_2(sK5,X0_46),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) != k1_connsp_2(sK5,X0_46) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3616]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3738,plain,
% 1.87/0.99      ( ~ m1_subset_1(k1_connsp_2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | m1_subset_1(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) != k1_connsp_2(sK5,sK6) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3736]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1,plain,
% 1.87/0.99      ( r2_hidden(sK2(X0,X1),X1)
% 1.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | ~ l1_pre_topc(X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_352,plain,
% 1.87/0.99      ( r2_hidden(sK2(X0,X1),X1)
% 1.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 1.87/0.99      | ~ v2_pre_topc(X0)
% 1.87/0.99      | sK5 != X0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_353,plain,
% 1.87/0.99      ( r2_hidden(sK2(sK5,X0),X0)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
% 1.87/0.99      | ~ v2_pre_topc(sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_352]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_357,plain,
% 1.87/0.99      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | r2_hidden(sK2(sK5,X0),X0) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_353,c_21]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_358,plain,
% 1.87/0.99      ( r2_hidden(sK2(sK5,X0),X0)
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_357]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3013,plain,
% 1.87/0.99      ( r2_hidden(sK2(sK5,X0_46),X0_46)
% 1.87/0.99      | ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_358]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3696,plain,
% 1.87/0.99      ( r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46))
% 1.87/0.99      | ~ m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3013]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3702,plain,
% 1.87/0.99      ( r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = iProver_top
% 1.87/0.99      | m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3696]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3704,plain,
% 1.87/0.99      ( r2_hidden(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) = iProver_top
% 1.87/0.99      | m1_subset_1(sK4(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3702]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_2,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.87/0.99      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
% 1.87/0.99      | ~ v2_pre_topc(X1)
% 1.87/0.99      | ~ l1_pre_topc(X1) ),
% 1.87/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_373,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 1.87/0.99      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X0),X1)
% 1.87/0.99      | ~ v2_pre_topc(X1)
% 1.87/0.99      | sK5 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_374,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
% 1.87/0.99      | ~ v2_pre_topc(sK5) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_373]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_378,plain,
% 1.87/0.99      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5)
% 1.87/0.99      | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_374,c_21]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_379,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | m1_subset_1(sK2(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0),sK5) ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_378]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3012,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | m1_subset_1(sK2(sK5,X0_46),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),X0_46),sK5) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_379]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3697,plain,
% 1.87/0.99      ( ~ m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 1.87/0.99      | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3012]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3698,plain,
% 1.87/0.99      ( m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 1.87/0.99      | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)),sK5) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3697]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3700,plain,
% 1.87/0.99      ( m1_subset_1(sK4(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 1.87/0.99      | m1_subset_1(sK2(sK5,sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 1.87/0.99      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)),sK5) = iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3698]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3630,plain,
% 1.87/0.99      ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
% 1.87/0.99      | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46)) = k1_connsp_2(sK5,X0_46) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3024]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3632,plain,
% 1.87/0.99      ( ~ sP0(k1_connsp_2(sK5,sK6),sK5,sK6)
% 1.87/0.99      | k6_setfam_1(u1_struct_0(sK5),sK4(k1_connsp_2(sK5,sK6),sK5,sK6)) = k1_connsp_2(sK5,sK6) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3630]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3625,plain,
% 1.87/0.99      ( ~ sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46)
% 1.87/0.99      | m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3019]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3626,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) != iProver_top
% 1.87/0.99      | m1_subset_1(sK4(k1_connsp_2(sK5,X0_46),sK5,X0_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3625]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3628,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) != iProver_top
% 1.87/0.99      | m1_subset_1(sK4(k1_connsp_2(sK5,sK6),sK5,sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3626]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3090,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,X0_46),sK5,X0_46) = iProver_top
% 1.87/0.99      | m1_subset_1(X0_46,u1_struct_0(sK5)) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_3014]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3092,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6) = iProver_top
% 1.87/0.99      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3090]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3091,plain,
% 1.87/0.99      ( sP0(k1_connsp_2(sK5,sK6),sK5,sK6)
% 1.87/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3014]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3016,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0_46,u1_struct_0(sK5))
% 1.87/0.99      | m1_subset_1(k1_connsp_2(sK5,X0_46),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.87/0.99      inference(subtyping,[status(esa)],[c_267]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_3085,plain,
% 1.87/0.99      ( m1_subset_1(k1_connsp_2(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.87/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 1.87/0.99      inference(instantiation,[status(thm)],[c_3016]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_18,negated_conjecture,
% 1.87/0.99      ( ~ v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) ),
% 1.87/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_27,plain,
% 1.87/0.99      ( v4_pre_topc(k1_connsp_2(sK5,sK6),sK5) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_26,plain,
% 1.87/0.99      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(contradiction,plain,
% 1.87/0.99      ( $false ),
% 1.87/0.99      inference(minisat,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_4311,c_4235,c_4019,c_3810,c_3750,c_3738,c_3704,c_3700,
% 1.87/0.99                 c_3632,c_3628,c_3092,c_3091,c_3085,c_27,c_26,c_19]) ).
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  ------                               Statistics
% 1.87/0.99  
% 1.87/0.99  ------ General
% 1.87/0.99  
% 1.87/0.99  abstr_ref_over_cycles:                  0
% 1.87/0.99  abstr_ref_under_cycles:                 0
% 1.87/0.99  gc_basic_clause_elim:                   0
% 1.87/0.99  forced_gc_time:                         0
% 1.87/0.99  parsing_time:                           0.008
% 1.87/0.99  unif_index_cands_time:                  0.
% 1.87/0.99  unif_index_add_time:                    0.
% 1.87/0.99  orderings_time:                         0.
% 1.87/0.99  out_proof_time:                         0.008
% 1.87/0.99  total_time:                             0.136
% 1.87/0.99  num_of_symbols:                         49
% 1.87/0.99  num_of_terms:                           2886
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing
% 1.87/0.99  
% 1.87/0.99  num_of_splits:                          0
% 1.87/0.99  num_of_split_atoms:                     0
% 1.87/0.99  num_of_reused_defs:                     0
% 1.87/0.99  num_eq_ax_congr_red:                    39
% 1.87/0.99  num_of_sem_filtered_clauses:            1
% 1.87/0.99  num_of_subtypes:                        3
% 1.87/0.99  monotx_restored_types:                  0
% 1.87/0.99  sat_num_of_epr_types:                   0
% 1.87/0.99  sat_num_of_non_cyclic_types:            0
% 1.87/0.99  sat_guarded_non_collapsed_types:        1
% 1.87/0.99  num_pure_diseq_elim:                    0
% 1.87/0.99  simp_replaced_by:                       0
% 1.87/0.99  res_preprocessed:                       99
% 1.87/0.99  prep_upred:                             0
% 1.87/0.99  prep_unflattend:                        269
% 1.87/0.99  smt_new_axioms:                         0
% 1.87/0.99  pred_elim_cands:                        5
% 1.87/0.99  pred_elim:                              4
% 1.87/0.99  pred_elim_cl:                           4
% 1.87/0.99  pred_elim_cycles:                       8
% 1.87/0.99  merged_defs:                            0
% 1.87/0.99  merged_defs_ncl:                        0
% 1.87/0.99  bin_hyper_res:                          0
% 1.87/0.99  prep_cycles:                            4
% 1.87/0.99  pred_elim_time:                         0.051
% 1.87/0.99  splitting_time:                         0.
% 1.87/0.99  sem_filter_time:                        0.
% 1.87/0.99  monotx_time:                            0.
% 1.87/0.99  subtype_inf_time:                       0.
% 1.87/0.99  
% 1.87/0.99  ------ Problem properties
% 1.87/0.99  
% 1.87/0.99  clauses:                                19
% 1.87/0.99  conjectures:                            2
% 1.87/0.99  epr:                                    0
% 1.87/0.99  horn:                                   13
% 1.87/0.99  ground:                                 2
% 1.87/0.99  unary:                                  2
% 1.87/0.99  binary:                                 4
% 1.87/0.99  lits:                                   62
% 1.87/0.99  lits_eq:                                2
% 1.87/0.99  fd_pure:                                0
% 1.87/0.99  fd_pseudo:                              0
% 1.87/0.99  fd_cond:                                0
% 1.87/0.99  fd_pseudo_cond:                         1
% 1.87/0.99  ac_symbols:                             0
% 1.87/0.99  
% 1.87/0.99  ------ Propositional Solver
% 1.87/0.99  
% 1.87/0.99  prop_solver_calls:                      26
% 1.87/0.99  prop_fast_solver_calls:                 1249
% 1.87/0.99  smt_solver_calls:                       0
% 1.87/0.99  smt_fast_solver_calls:                  0
% 1.87/0.99  prop_num_of_clauses:                    762
% 1.87/0.99  prop_preprocess_simplified:             3916
% 1.87/0.99  prop_fo_subsumed:                       12
% 1.87/0.99  prop_solver_time:                       0.
% 1.87/0.99  smt_solver_time:                        0.
% 1.87/0.99  smt_fast_solver_time:                   0.
% 1.87/0.99  prop_fast_solver_time:                  0.
% 1.87/0.99  prop_unsat_core_time:                   0.
% 1.87/0.99  
% 1.87/0.99  ------ QBF
% 1.87/0.99  
% 1.87/0.99  qbf_q_res:                              0
% 1.87/0.99  qbf_num_tautologies:                    0
% 1.87/0.99  qbf_prep_cycles:                        0
% 1.87/0.99  
% 1.87/0.99  ------ BMC1
% 1.87/0.99  
% 1.87/0.99  bmc1_current_bound:                     -1
% 1.87/0.99  bmc1_last_solved_bound:                 -1
% 1.87/0.99  bmc1_unsat_core_size:                   -1
% 1.87/0.99  bmc1_unsat_core_parents_size:           -1
% 1.87/0.99  bmc1_merge_next_fun:                    0
% 1.87/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation
% 1.87/0.99  
% 1.87/0.99  inst_num_of_clauses:                    151
% 1.87/0.99  inst_num_in_passive:                    24
% 1.87/0.99  inst_num_in_active:                     95
% 1.87/0.99  inst_num_in_unprocessed:                32
% 1.87/0.99  inst_num_of_loops:                      100
% 1.87/0.99  inst_num_of_learning_restarts:          0
% 1.87/0.99  inst_num_moves_active_passive:          2
% 1.87/0.99  inst_lit_activity:                      0
% 1.87/0.99  inst_lit_activity_moves:                0
% 1.87/0.99  inst_num_tautologies:                   0
% 1.87/0.99  inst_num_prop_implied:                  0
% 1.87/0.99  inst_num_existing_simplified:           0
% 1.87/0.99  inst_num_eq_res_simplified:             0
% 1.87/0.99  inst_num_child_elim:                    0
% 1.87/0.99  inst_num_of_dismatching_blockings:      4
% 1.87/0.99  inst_num_of_non_proper_insts:           116
% 1.87/0.99  inst_num_of_duplicates:                 0
% 1.87/0.99  inst_inst_num_from_inst_to_res:         0
% 1.87/0.99  inst_dismatching_checking_time:         0.
% 1.87/0.99  
% 1.87/0.99  ------ Resolution
% 1.87/0.99  
% 1.87/0.99  res_num_of_clauses:                     0
% 1.87/0.99  res_num_in_passive:                     0
% 1.87/0.99  res_num_in_active:                      0
% 1.87/0.99  res_num_of_loops:                       103
% 1.87/0.99  res_forward_subset_subsumed:            0
% 1.87/0.99  res_backward_subset_subsumed:           0
% 1.87/0.99  res_forward_subsumed:                   0
% 1.87/0.99  res_backward_subsumed:                  0
% 1.87/0.99  res_forward_subsumption_resolution:     4
% 1.87/0.99  res_backward_subsumption_resolution:    0
% 1.87/0.99  res_clause_to_clause_subsumption:       88
% 1.87/0.99  res_orphan_elimination:                 0
% 1.87/0.99  res_tautology_del:                      20
% 1.87/0.99  res_num_eq_res_simplified:              0
% 1.87/0.99  res_num_sel_changes:                    0
% 1.87/0.99  res_moves_from_active_to_pass:          0
% 1.87/0.99  
% 1.87/0.99  ------ Superposition
% 1.87/0.99  
% 1.87/0.99  sup_time_total:                         0.
% 1.87/0.99  sup_time_generating:                    0.
% 1.87/0.99  sup_time_sim_full:                      0.
% 1.87/0.99  sup_time_sim_immed:                     0.
% 1.87/0.99  
% 1.87/0.99  sup_num_of_clauses:                     29
% 1.87/0.99  sup_num_in_active:                      19
% 1.87/0.99  sup_num_in_passive:                     10
% 1.87/0.99  sup_num_of_loops:                       18
% 1.87/0.99  sup_fw_superposition:                   5
% 1.87/0.99  sup_bw_superposition:                   5
% 1.87/0.99  sup_immediate_simplified:               0
% 1.87/0.99  sup_given_eliminated:                   0
% 1.87/0.99  comparisons_done:                       0
% 1.87/0.99  comparisons_avoided:                    0
% 1.87/0.99  
% 1.87/0.99  ------ Simplifications
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  sim_fw_subset_subsumed:                 0
% 1.87/0.99  sim_bw_subset_subsumed:                 0
% 1.87/0.99  sim_fw_subsumed:                        0
% 1.87/0.99  sim_bw_subsumed:                        0
% 1.87/0.99  sim_fw_subsumption_res:                 0
% 1.87/0.99  sim_bw_subsumption_res:                 0
% 1.87/0.99  sim_tautology_del:                      0
% 1.87/0.99  sim_eq_tautology_del:                   1
% 1.87/0.99  sim_eq_res_simp:                        0
% 1.87/0.99  sim_fw_demodulated:                     0
% 1.87/0.99  sim_bw_demodulated:                     0
% 1.87/0.99  sim_light_normalised:                   0
% 1.87/0.99  sim_joinable_taut:                      0
% 1.87/0.99  sim_joinable_simp:                      0
% 1.87/0.99  sim_ac_normalised:                      0
% 1.87/0.99  sim_smt_subsumption:                    0
% 1.87/0.99  
%------------------------------------------------------------------------------
