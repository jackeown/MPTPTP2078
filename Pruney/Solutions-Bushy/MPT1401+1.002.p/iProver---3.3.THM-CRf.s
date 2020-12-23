%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1401+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:38 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 344 expanded)
%              Number of clauses        :   74 (  93 expanded)
%              Number of leaves         :   18 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  615 (2839 expanded)
%              Number of equality atoms :  106 ( 359 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( k1_connsp_2(X0,X1) = X2
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_connsp_2(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k1_connsp_2(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_connsp_2(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k1_connsp_2(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_connsp_2(X1,X0) = X2
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f17,plain,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f18,f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f16,f33,f32,f31])).

fof(f59,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,sK3(X0,X1,X2))
      | ~ r2_hidden(X2,X6)
      | ~ v4_pre_topc(X6,X1)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_connsp_2(X1,X0) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP0(k1_connsp_2(X1,X0),X1,X0)
      | ~ sP1(X0,X1,k1_connsp_2(X1,X0)) ) ),
    inference(equality_resolution,[],[f38])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f66,plain,(
    k1_connsp_2(sK4,sK5) != sK6 ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    r1_tarski(sK6,k1_connsp_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    v4_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3586,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4559,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_connsp_2(sK4,sK5),sK6)
    | k1_connsp_2(sK4,sK5) != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_4844,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(k1_connsp_2(sK4,sK5),sK6)
    | k1_connsp_2(sK4,sK5) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4559])).

cnf(c_9758,plain,
    ( ~ r1_tarski(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6)
    | r1_tarski(k1_connsp_2(sK4,sK5),sK6)
    | k1_connsp_2(sK4,sK5) != k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4844])).

cnf(c_4781,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK6)
    | X2 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_5476,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(X1,sK6)
    | X1 != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4781])).

cnf(c_6398,plain,
    ( r1_tarski(X0,sK6)
    | ~ r1_tarski(k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6)
    | X0 != k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_5476])).

cnf(c_7671,plain,
    ( r1_tarski(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6)
    | ~ r1_tarski(k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6)
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_6398])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4503,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_6773,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4503])).

cnf(c_4654,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_struct_0(X3))
    | X2 != X0
    | u1_struct_0(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_4995,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | r1_tarski(X2,u1_struct_0(X1))
    | X2 != X0
    | u1_struct_0(X1) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_4654])).

cnf(c_5765,plain,
    ( r1_tarski(X0,u1_struct_0(sK4))
    | ~ r1_tarski(k1_connsp_2(sK4,sK5),u1_struct_0(sK4))
    | X0 != k1_connsp_2(sK4,sK5)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4995])).

cnf(c_6306,plain,
    ( r1_tarski(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),u1_struct_0(sK4))
    | ~ r1_tarski(k1_connsp_2(sK4,sK5),u1_struct_0(sK4))
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_connsp_2(sK4,sK5)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5765])).

cnf(c_3,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k1_connsp_2(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_422,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_423,plain,
    ( sP1(X0,sK4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_427,plain,
    ( sP1(X0,sK4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_31,c_30])).

cnf(c_450,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | X4 != X2
    | X3 != X0
    | k1_connsp_2(X1,X2) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_427])).

cnf(c_451,plain,
    ( ~ sP0(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k1_connsp_2(sK4,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_4447,plain,
    ( ~ sP0(X0,sK4,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k1_connsp_2(sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_5089,plain,
    ( ~ sP0(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK4,sK5)
    | ~ m1_subset_1(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | k1_connsp_2(sK4,sK5) = k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4447])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5006,plain,
    ( ~ r2_hidden(sK6,sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | r1_tarski(k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4917,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_connsp_2(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4639])).

cnf(c_3588,plain,
    ( ~ sP0(X0,X1,X2)
    | sP0(X3,X4,X2)
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_4545,plain,
    ( sP0(X0,X1,sK5)
    | ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | X0 != k1_connsp_2(sK4,sK5)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_3588])).

cnf(c_4827,plain,
    ( sP0(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),X0,sK5)
    | ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | X0 != sK4
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_connsp_2(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_4545])).

cnf(c_4829,plain,
    ( sP0(k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)),sK4,sK5)
    | ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) != k1_connsp_2(sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4827])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4725,plain,
    ( ~ m1_subset_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) = k1_setfam_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4520,plain,
    ( ~ sP0(X0,sK4,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK6,sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | ~ r2_hidden(X1,sK6)
    | r2_hidden(sK6,sK3(X0,sK4,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4614,plain,
    ( ~ sP0(X0,sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK6,sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | r2_hidden(sK6,sK3(X0,sK4,sK5))
    | ~ r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4520])).

cnf(c_4697,plain,
    ( ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(sK6,sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | r2_hidden(sK6,sK3(k1_connsp_2(sK4,sK5),sK4,sK5))
    | ~ r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4614])).

cnf(c_3584,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4580,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3584])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | k6_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4546,plain,
    ( ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | k6_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_2(sK4,sK5),sK4,sK5)) = k1_connsp_2(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4547,plain,
    ( ~ sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | m1_subset_1(sK3(k1_connsp_2(sK4,sK5),sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4463,plain,
    ( ~ r1_tarski(k1_connsp_2(sK4,sK5),sK6)
    | ~ r1_tarski(sK6,k1_connsp_2(sK4,sK5))
    | k1_connsp_2(sK4,sK5) = sK6 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ sP1(X0,X1,k1_connsp_2(X1,X0))
    | sP0(k1_connsp_2(X1,X0),X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_468,plain,
    ( sP0(k1_connsp_2(X0,X1),X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | X3 != X1
    | k1_connsp_2(X0,X1) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_427])).

cnf(c_469,plain,
    ( sP0(k1_connsp_2(sK4,X0),sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_31,c_30])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | sP0(k1_connsp_2(sK4,X0),sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_31,c_30,c_405])).

cnf(c_474,plain,
    ( sP0(k1_connsp_2(sK4,X0),sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_4444,plain,
    ( sP0(k1_connsp_2(sK4,sK5),sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_4441,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_3589,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3599,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3589])).

cnf(c_103,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_99,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_22,negated_conjecture,
    ( k1_connsp_2(sK4,sK5) != sK6 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK6,k1_connsp_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v4_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9758,c_7671,c_6773,c_6306,c_5089,c_5006,c_4917,c_4829,c_4725,c_4697,c_4580,c_4546,c_4547,c_4463,c_4444,c_4441,c_3599,c_103,c_99,c_22,c_23,c_24,c_25,c_26,c_27,c_28])).


%------------------------------------------------------------------------------
