%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:37 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 616 expanded)
%              Number of clauses        :   97 ( 169 expanded)
%              Number of leaves         :   19 ( 202 expanded)
%              Depth                    :   20
%              Number of atoms          :  678 (4143 expanded)
%              Number of equality atoms :  116 ( 613 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_1(X0,X1) = X2
              <=> ? [X3] :
                    ( k5_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v2_connsp_1(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_1(X0,X1) = X2
              <=> ? [X3] :
                    ( k5_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v2_connsp_1(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( k1_connsp_1(X0,X1) = X2
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ? [X3] :
          ( k5_setfam_1(u1_struct_0(X0),X3) = X2
          & ! [X4] :
              ( ( r2_hidden(X4,X3)
              <=> ( r2_hidden(X1,X4)
                  & v2_connsp_1(X4,X0) ) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f32,f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_connsp_1(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k1_connsp_1(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_connsp_1(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k1_connsp_1(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_connsp_1(X1,X0) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sP0(k1_connsp_1(X1,X0),X1,X0)
      | ~ sP1(X0,X1,k1_connsp_1(X1,X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( X2 = X3
                   => r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ( X2 = X3
                     => r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
                  & X2 = X3
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
                  & X2 = X3
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
          & X2 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tarski(k1_connsp_1(X1,sK7),k1_connsp_1(X0,X2))
        & sK7 = X2
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
              & X2 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,sK6))
            & sK6 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
                  & X2 = X3
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k1_connsp_1(sK5,X3),k1_connsp_1(X0,X2))
                & X2 = X3
                & m1_subset_1(X3,u1_struct_0(sK5)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
                    & X2 = X3
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(sK4,X2))
                  & X2 = X3
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r1_tarski(k1_connsp_1(sK5,sK7),k1_connsp_1(sK4,sK6))
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f30,f46,f45,f44,f43])).

fof(f72,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ! [X3] :
            ( k5_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ( ~ r2_hidden(X1,X4)
                  | ~ v2_connsp_1(X4,X0)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X1,X4)
                    & v2_connsp_1(X4,X0) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k5_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( ( ( r2_hidden(X4,X3)
                    | ~ r2_hidden(X1,X4)
                    | ~ v2_connsp_1(X4,X0) )
                  & ( ( r2_hidden(X1,X4)
                      & v2_connsp_1(X4,X0) )
                    | ~ r2_hidden(X4,X3) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ! [X3] :
            ( k5_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ( ~ r2_hidden(X1,X4)
                  | ~ v2_connsp_1(X4,X0)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X1,X4)
                    & v2_connsp_1(X4,X0) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k5_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( ( ( r2_hidden(X4,X3)
                    | ~ r2_hidden(X1,X4)
                    | ~ v2_connsp_1(X4,X0) )
                  & ( ( r2_hidden(X1,X4)
                      & v2_connsp_1(X4,X0) )
                    | ~ r2_hidden(X4,X3) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k5_setfam_1(u1_struct_0(X1),X3) != X0
            | ? [X4] :
                ( ( ~ r2_hidden(X2,X4)
                  | ~ v2_connsp_1(X4,X1)
                  | ~ r2_hidden(X4,X3) )
                & ( ( r2_hidden(X2,X4)
                    & v2_connsp_1(X4,X1) )
                  | r2_hidden(X4,X3) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ? [X5] :
            ( k5_setfam_1(u1_struct_0(X1),X5) = X0
            & ! [X6] :
                ( ( ( r2_hidden(X6,X5)
                    | ~ r2_hidden(X2,X6)
                    | ~ v2_connsp_1(X6,X1) )
                  & ( ( r2_hidden(X2,X6)
                      & v2_connsp_1(X6,X1) )
                    | ~ r2_hidden(X6,X5) ) )
                | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k5_setfam_1(u1_struct_0(X1),X5) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,X5)
                  | ~ r2_hidden(X2,X6)
                  | ~ v2_connsp_1(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v2_connsp_1(X6,X1) )
                  | ~ r2_hidden(X6,X5) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( k5_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0
        & ! [X6] :
            ( ( ( r2_hidden(X6,sK3(X0,X1,X2))
                | ~ r2_hidden(X2,X6)
                | ~ v2_connsp_1(X6,X1) )
              & ( ( r2_hidden(X2,X6)
                  & v2_connsp_1(X6,X1) )
                | ~ r2_hidden(X6,sK3(X0,X1,X2)) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ~ r2_hidden(X2,X4)
            | ~ v2_connsp_1(X4,X1)
            | ~ r2_hidden(X4,X3) )
          & ( ( r2_hidden(X2,X4)
              & v2_connsp_1(X4,X1) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ~ r2_hidden(X2,sK2(X1,X2,X3))
          | ~ v2_connsp_1(sK2(X1,X2,X3),X1)
          | ~ r2_hidden(sK2(X1,X2,X3),X3) )
        & ( ( r2_hidden(X2,sK2(X1,X2,X3))
            & v2_connsp_1(sK2(X1,X2,X3),X1) )
          | r2_hidden(sK2(X1,X2,X3),X3) )
        & m1_subset_1(sK2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k5_setfam_1(u1_struct_0(X1),X3) != X0
            | ( ( ~ r2_hidden(X2,sK2(X1,X2,X3))
                | ~ v2_connsp_1(sK2(X1,X2,X3),X1)
                | ~ r2_hidden(sK2(X1,X2,X3),X3) )
              & ( ( r2_hidden(X2,sK2(X1,X2,X3))
                  & v2_connsp_1(sK2(X1,X2,X3),X1) )
                | r2_hidden(sK2(X1,X2,X3),X3) )
              & m1_subset_1(sK2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ( k5_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0
          & ! [X6] :
              ( ( ( r2_hidden(X6,sK3(X0,X1,X2))
                  | ~ r2_hidden(X2,X6)
                  | ~ v2_connsp_1(X6,X1) )
                & ( ( r2_hidden(X2,X6)
                    & v2_connsp_1(X6,X1) )
                  | ~ r2_hidden(X6,sK3(X0,X1,X2)) ) )
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,sK3(X0,X1,X2))
      | ~ r2_hidden(X2,X6)
      | ~ v2_connsp_1(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f47])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k5_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ~ r1_tarski(k1_connsp_1(sK5,sK7),k1_connsp_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
        & ~ v1_xboole_0(k1_connsp_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => v2_connsp_1(k1_connsp_1(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_1(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_1(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_connsp_1(X2,X0)
                    <=> v2_connsp_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_connsp_1(X2,X0)
                      | ~ v2_connsp_1(X3,X1) )
                    & ( v2_connsp_1(X3,X1)
                      | ~ v2_connsp_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(X2,X0)
      | ~ v2_connsp_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( v2_connsp_1(X3,X0)
      | ~ v2_connsp_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

cnf(c_12,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( ~ sP1(X0,X1,k1_connsp_1(X1,X0))
    | sP0(k1_connsp_1(X1,X0),X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_362,plain,
    ( sP0(k1_connsp_1(X0,X1),X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_pre_topc(X3)
    | X1 != X4
    | X0 != X3
    | k1_connsp_1(X0,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_2])).

cnf(c_363,plain,
    ( sP0(k1_connsp_1(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_375,plain,
    ( sP0(k1_connsp_1(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_13])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_667,plain,
    ( sP0(k1_connsp_1(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_375,c_28])).

cnf(c_668,plain,
    ( sP0(k1_connsp_1(sK4,X0),sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_2902,plain,
    ( sP0(k1_connsp_1(sK4,X0_49),sK4,X0_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_668])).

cnf(c_3459,plain,
    ( sP0(k1_connsp_1(sK4,X0_49),sK4,X0_49) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2902])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_connsp_1(X3,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2922,plain,
    ( ~ sP0(X0_49,X0_50,X1_49)
    | ~ m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(X0_50)))
    | ~ v2_connsp_1(X2_49,X0_50)
    | ~ r2_hidden(X1_49,X2_49)
    | r2_hidden(X2_49,sK3(X0_49,X0_50,X1_49)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3440,plain,
    ( sP0(X0_49,X0_50,X1_49) != iProver_top
    | m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(X0_50))) != iProver_top
    | v2_connsp_1(X2_49,X0_50) != iProver_top
    | r2_hidden(X1_49,X2_49) != iProver_top
    | r2_hidden(X2_49,sK3(X0_49,X0_50,X1_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2922])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2915,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3446,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2915])).

cnf(c_23,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2917,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3465,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3446,c_2917])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2919,plain,
    ( ~ sP0(X0_49,X0_50,X1_49)
    | m1_subset_1(sK3(X0_49,X0_50,X1_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_50)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3443,plain,
    ( sP0(X0_49,X0_50,X1_49) != iProver_top
    | m1_subset_1(sK3(X0_49,X0_50,X1_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_50)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2919])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2918,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k1_zfmisc_1(X0_51)))
    | k5_setfam_1(X0_51,X0_49) = k3_tarski(X0_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3444,plain,
    ( k5_setfam_1(X0_51,X0_49) = k3_tarski(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k1_zfmisc_1(X0_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2918])).

cnf(c_4037,plain,
    ( k5_setfam_1(u1_struct_0(X0_50),sK3(X0_49,X0_50,X1_49)) = k3_tarski(sK3(X0_49,X0_50,X1_49))
    | sP0(X0_49,X0_50,X1_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_3443,c_3444])).

cnf(c_5361,plain,
    ( k5_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_1(sK4,X0_49),sK4,X0_49)) = k3_tarski(sK3(k1_connsp_1(sK4,X0_49),sK4,X0_49))
    | m1_subset_1(X0_49,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3459,c_4037])).

cnf(c_5712,plain,
    ( k5_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_1(sK4,sK7),sK4,sK7)) = k3_tarski(sK3(k1_connsp_1(sK4,sK7),sK4,sK7)) ),
    inference(superposition,[status(thm)],[c_3465,c_5361])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2)
    | k5_setfam_1(u1_struct_0(X1),sK3(X0,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2923,plain,
    ( ~ sP0(X0_49,X0_50,X1_49)
    | k5_setfam_1(u1_struct_0(X0_50),sK3(X0_49,X0_50,X1_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3439,plain,
    ( k5_setfam_1(u1_struct_0(X0_50),sK3(X0_49,X0_50,X1_49)) = X0_49
    | sP0(X0_49,X0_50,X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2923])).

cnf(c_4030,plain,
    ( k5_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_1(sK4,X0_49),sK4,X0_49)) = k1_connsp_1(sK4,X0_49)
    | m1_subset_1(X0_49,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3459,c_3439])).

cnf(c_4926,plain,
    ( k5_setfam_1(u1_struct_0(sK4),sK3(k1_connsp_1(sK4,sK7),sK4,sK7)) = k1_connsp_1(sK4,sK7) ),
    inference(superposition,[status(thm)],[c_3465,c_4030])).

cnf(c_5713,plain,
    ( k3_tarski(sK3(k1_connsp_1(sK4,sK7),sK4,sK7)) = k1_connsp_1(sK4,sK7) ),
    inference(light_normalisation,[status(thm)],[c_5712,c_4926])).

cnf(c_21,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k1_connsp_1(sK5,sK7),k1_connsp_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_327,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_connsp_1(sK4,sK6) != k3_tarski(X1)
    | k1_connsp_1(sK5,sK7) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_22])).

cnf(c_328,plain,
    ( ~ r2_hidden(k1_connsp_1(sK5,sK7),X0)
    | k1_connsp_1(sK4,sK6) != k3_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_2914,plain,
    ( ~ r2_hidden(k1_connsp_1(sK5,sK7),X0_49)
    | k1_connsp_1(sK4,sK6) != k3_tarski(X0_49) ),
    inference(subtyping,[status(esa)],[c_328])).

cnf(c_3447,plain,
    ( k1_connsp_1(sK4,sK6) != k3_tarski(X0_49)
    | r2_hidden(k1_connsp_1(sK5,sK7),X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_3488,plain,
    ( k1_connsp_1(sK4,sK7) != k3_tarski(X0_49)
    | r2_hidden(k1_connsp_1(sK5,sK7),X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3447,c_2917])).

cnf(c_5715,plain,
    ( r2_hidden(k1_connsp_1(sK5,sK7),sK3(k1_connsp_1(sK4,sK7),sK4,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5713,c_3488])).

cnf(c_5817,plain,
    ( sP0(k1_connsp_1(sK4,sK7),sK4,sK7) != iProver_top
    | m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_connsp_1(k1_connsp_1(sK5,sK7),sK4) != iProver_top
    | r2_hidden(sK7,k1_connsp_1(sK5,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3440,c_5715])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_37,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_480,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK4 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_481,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_483,plain,
    ( l1_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_28])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_483])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k1_connsp_1(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_2903,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
    | m1_subset_1(k1_connsp_1(sK5,X0_49),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_656])).

cnf(c_3679,plain,
    ( m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2903])).

cnf(c_3680,plain,
    ( m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3679])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_491,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK4 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_492,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_494,plain,
    ( v2_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_29,c_28])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_connsp_1(k1_connsp_1(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_connsp_1(k1_connsp_1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_connsp_1(k1_connsp_1(sK5,X0),sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_connsp_1(k1_connsp_1(sK5,X0),sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_483,c_411])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_connsp_1(k1_connsp_1(sK5,X0),sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_494,c_578])).

cnf(c_2908,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
    | v2_connsp_1(k1_connsp_1(sK5,X0_49),sK5) ),
    inference(subtyping,[status(esa)],[c_587])).

cnf(c_3682,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v2_connsp_1(k1_connsp_1(sK5,sK7),sK5) ),
    inference(instantiation,[status(thm)],[c_2908])).

cnf(c_3683,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | v2_connsp_1(k1_connsp_1(sK5,sK7),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3682])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k1_connsp_1(sK5,X0))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k1_connsp_1(sK5,X0))
    | ~ v2_pre_topc(sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_483,c_393])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k1_connsp_1(sK5,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_494,c_577])).

cnf(c_2907,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK5))
    | r2_hidden(X0_49,k1_connsp_1(sK5,X0_49)) ),
    inference(subtyping,[status(esa)],[c_588])).

cnf(c_3688,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,k1_connsp_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_2907])).

cnf(c_3689,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,k1_connsp_1(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3688])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK4 != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_551,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_28])).

cnf(c_556,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_555])).

cnf(c_2911,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_556])).

cnf(c_3765,plain,
    ( m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2911])).

cnf(c_3766,plain,
    ( m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3765])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_connsp_1(X0,X2)
    | v2_connsp_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_connsp_1(X0,X2)
    | v2_connsp_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_connsp_1(X0,sK4)
    | ~ v2_connsp_1(X0,sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_connsp_1(X0,sK4)
    | ~ v2_connsp_1(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_29,c_28])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_connsp_1(X0,sK4)
    | ~ v2_connsp_1(X0,sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_556,c_531])).

cnf(c_2909,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_connsp_1(X0_49,sK4)
    | ~ v2_connsp_1(X0_49,sK5) ),
    inference(subtyping,[status(esa)],[c_567])).

cnf(c_3783,plain,
    ( ~ m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_connsp_1(k1_connsp_1(sK5,sK7),sK4)
    | ~ v2_connsp_1(k1_connsp_1(sK5,sK7),sK5) ),
    inference(instantiation,[status(thm)],[c_2909])).

cnf(c_3784,plain,
    ( m1_subset_1(k1_connsp_1(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_connsp_1(k1_connsp_1(sK5,sK7),sK4) = iProver_top
    | v2_connsp_1(k1_connsp_1(sK5,sK7),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3783])).

cnf(c_5820,plain,
    ( sP0(k1_connsp_1(sK4,sK7),sK4,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5817,c_37,c_3680,c_3683,c_3689,c_3766,c_3784])).

cnf(c_5825,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3459,c_5820])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5825,c_3465])).


%------------------------------------------------------------------------------
