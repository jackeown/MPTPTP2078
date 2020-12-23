%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1401+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:38 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 335 expanded)
%              Number of clauses        :   72 (  90 expanded)
%              Number of leaves         :   19 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  601 (2815 expanded)
%              Number of equality atoms :  112 ( 363 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( k1_connsp_2(X0,X1) = X2
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_connsp_2(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k1_connsp_2(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_connsp_2(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k1_connsp_2(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_connsp_2(X1,X0) = X2
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f19,plain,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f20,f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                  & r2_hidden(X1,X2)
                  & v4_pre_topc(X2,X0)
                  & v3_pre_topc(X2,X0) )
               => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                    & r2_hidden(X1,X2)
                    & v4_pre_topc(X2,X0)
                    & v3_pre_topc(X2,X0) )
                 => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_connsp_2(X0,X1) != X2
          & r1_tarski(X2,k1_connsp_2(X0,X1))
          & r2_hidden(X1,X2)
          & v4_pre_topc(X2,X0)
          & v3_pre_topc(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_connsp_2(X0,X1) != sK6
        & r1_tarski(sK6,k1_connsp_2(X0,X1))
        & r2_hidden(X1,sK6)
        & v4_pre_topc(sK6,X0)
        & v3_pre_topc(sK6,X0)
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_connsp_2(X0,sK5) != X2
            & r1_tarski(X2,k1_connsp_2(X0,sK5))
            & r2_hidden(sK5,X2)
            & v4_pre_topc(X2,X0)
            & v3_pre_topc(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_connsp_2(X0,X1) != X2
                & r1_tarski(X2,k1_connsp_2(X0,X1))
                & r2_hidden(X1,X2)
                & v4_pre_topc(X2,X0)
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(sK4,X1) != X2
              & r1_tarski(X2,k1_connsp_2(sK4,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,sK4)
              & v3_pre_topc(X2,sK4)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_connsp_2(sK4,sK5) != sK6
    & r1_tarski(sK6,k1_connsp_2(sK4,sK5))
    & r2_hidden(sK5,sK6)
    & v4_pre_topc(sK6,sK4)
    & v3_pre_topc(sK6,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f18,f34,f33,f32])).

fof(f59,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,sK3(X0,X1,X2))
      | ~ r2_hidden(X2,X6)
      | ~ v4_pre_topc(X6,X1)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_connsp_2(X1,X0) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP0(k1_connsp_2(X1,X0),X1,X0)
      | ~ sP1(X0,X1,k1_connsp_2(X1,X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f66,plain,(
    k1_connsp_2(sK4,sK5) != sK6 ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    r1_tarski(sK6,k1_connsp_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    v4_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3450,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4237,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_connsp_2(sK4,sK5),sK6)
    | k1_connsp_2(sK4,sK5) != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_3450])).

cnf(c_4518,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(k1_connsp_2(sK4,sK5),sK6)
    | k1_connsp_2(sK4,sK5) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4237])).

cnf(c_9819,plain,
    ( ~ r1_tarski(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6)
    | r1_tarski(k1_connsp_2(sK4,sK5),sK6)
    | k1_connsp_2(sK4,sK5) != k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4518])).

cnf(c_4420,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK6)
    | X2 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_3450])).

cnf(c_4901,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(X1,sK6)
    | X1 != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4420])).

cnf(c_5812,plain,
    ( r1_tarski(X0,sK6)
    | ~ r1_tarski(k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6)
    | X0 != k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4901])).

cnf(c_6838,plain,
    ( r1_tarski(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6)
    | ~ r1_tarski(k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6)
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_5812])).

cnf(c_3459,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4216,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_connsp_2(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != k1_connsp_2(sK4,sK5)
    | X1 != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3459])).

cnf(c_4494,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),X0)
    | ~ m1_subset_1(k1_connsp_2(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK4))
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_connsp_2(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_4216])).

cnf(c_4664,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_connsp_2(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_connsp_2(sK4,sK5)
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4494])).

cnf(c_3458,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4401,plain,
    ( X0 != u1_struct_0(sK4)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_4652,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4401])).

cnf(c_3,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k1_connsp_2(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_347,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_348,plain,
    ( sP1(X0,sK4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_352,plain,
    ( sP1(X0,sK4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_30,c_29])).

cnf(c_375,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | X4 != X2
    | X3 != X0
    | k1_connsp_2(X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_352])).

cnf(c_376,plain,
    ( ~ sP0(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k1_connsp_2(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_4137,plain,
    ( ~ sP0(X0,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k1_connsp_2(sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_4635,plain,
    ( ~ sP0(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK4,sK5)
    | ~ m1_subset_1(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k1_connsp_2(sK4,sK5) = k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4137])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4317,plain,
    ( ~ r2_hidden(sK6,sK3(X0,sK4,sK5))
    | r1_tarski(k1_setfam_1(sK3(X0,sK4,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4576,plain,
    ( ~ r2_hidden(sK6,sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | r1_tarski(k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_4317])).

cnf(c_3452,plain,
    ( ~ sP0(X0,X1,X2)
    | sP0(X3,X4,X2)
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_4226,plain,
    ( sP0(X0,X1,sK5)
    | ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | X0 != k1_connsp_2(sK4,sK5)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_3452])).

cnf(c_4506,plain,
    ( sP0(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),X0,sK5)
    | ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | X0 != sK4
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_connsp_2(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_4226])).

cnf(c_4508,plain,
    ( sP0(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK4,sK5)
    | ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_connsp_2(sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4506])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4198,plain,
    ( ~ sP0(X0,sK4,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK6,sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | ~ r2_hidden(X1,sK6)
    | r2_hidden(sK6,sK3(X0,sK4,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4297,plain,
    ( ~ sP0(X0,sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK6,sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | r2_hidden(sK6,sK3(X0,sK4,sK5))
    | ~ r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4198])).

cnf(c_4416,plain,
    ( ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK6,sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | r2_hidden(sK6,sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | ~ r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4297])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4362,plain,
    ( ~ m1_subset_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) = k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3448,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4259,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3448])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | k6_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4227,plain,
    ( ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) = k1_connsp_2(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4228,plain,
    ( ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | m1_subset_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4148,plain,
    ( ~ r1_tarski(k1_connsp_2(sK4,sK5),sK6)
    | ~ r1_tarski(sK6,k1_connsp_2(sK4,sK5))
    | k1_connsp_2(sK4,sK5) = sK6 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,k1_connsp_2(X1,X0))
    | sP0(k1_connsp_2(X1,X0),X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_393,plain,
    ( sP0(k1_connsp_2(X0,X1),X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | X3 != X1
    | k1_connsp_2(X0,X1) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_352])).

cnf(c_394,plain,
    ( sP0(k1_connsp_2(sK4,X0),sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_30,c_29])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | sP0(k1_connsp_2(sK4,X0),sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_30,c_29,c_330])).

cnf(c_399,plain,
    ( sP0(k1_connsp_2(sK4,X0),sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_398])).

cnf(c_4134,plain,
    ( sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_4131,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_3453,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3463,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3453])).

cnf(c_99,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_95,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_21,negated_conjecture,
    ( k1_connsp_2(sK4,sK5) != sK6 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK6,k1_connsp_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( v4_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,negated_conjecture,
    ( v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9819,c_6838,c_4664,c_4652,c_4635,c_4576,c_4508,c_4416,c_4362,c_4259,c_4227,c_4228,c_4148,c_4134,c_4131,c_3463,c_99,c_95,c_21,c_22,c_23,c_24,c_25,c_26,c_27])).


%------------------------------------------------------------------------------
