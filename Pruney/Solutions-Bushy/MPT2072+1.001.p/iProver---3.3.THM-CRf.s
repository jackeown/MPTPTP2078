%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2072+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:08 EST 2020

% Result     : Theorem 51.90s
% Output     : CNFRefutation 51.90s
% Verified   : 
% Statistics : Number of formulae       :  310 (12132 expanded)
%              Number of clauses        :  221 (3583 expanded)
%              Number of leaves         :   24 (2938 expanded)
%              Depth                    :   33
%              Number of atoms          : 1165 (73227 expanded)
%              Number of equality atoms :  467 (10567 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k2_cantor_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> ? [X4] :
                      ( k8_setfam_1(X0,X4) = X3
                      & v1_finset_1(X4)
                      & r1_tarski(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_cantor_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> ? [X4] :
                      ( k8_setfam_1(X0,X4) = X3
                      & v1_finset_1(X4)
                      & r1_tarski(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ( k2_cantor_1(X0,X1) = X2
      <=> sP0(X0,X1,X2) )
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ? [X4] :
                ( k8_setfam_1(X0,X4) = X3
                & v1_finset_1(X4)
                & r1_tarski(X4,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f20,f35,f34])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( ( k2_cantor_1(X0,X1) = X2
          | ~ sP0(X0,X1,X2) )
        & ( sP0(X0,X1,X2)
          | k2_cantor_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_cantor_1(X2,X1) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_cantor_1(X2,X1) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_cantor_1(X2,X1) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_cantor_1(X2,X1))
      | ~ sP1(k2_cantor_1(X2,X1),X1,X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k8_setfam_1(X0,X4) != X3
                  | ~ v1_finset_1(X4)
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( k8_setfam_1(X0,X4) = X3
                  & v1_finset_1(X4)
                  & r1_tarski(X4,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( k8_setfam_1(X0,X4) != X3
                    | ~ v1_finset_1(X4)
                    | ~ r1_tarski(X4,X1)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )
              & ( ? [X4] :
                    ( k8_setfam_1(X0,X4) = X3
                    & v1_finset_1(X4)
                    & r1_tarski(X4,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k8_setfam_1(X0,X4) != X3
                  | ~ v1_finset_1(X4)
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( k8_setfam_1(X0,X4) = X3
                  & v1_finset_1(X4)
                  & r1_tarski(X4,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( k8_setfam_1(X0,X4) != X3
                    | ~ v1_finset_1(X4)
                    | ~ r1_tarski(X4,X1)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )
              & ( ? [X4] :
                    ( k8_setfam_1(X0,X4) = X3
                    & v1_finset_1(X4)
                    & r1_tarski(X4,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k8_setfam_1(X0,X4) != X3
                  | ~ v1_finset_1(X4)
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( k8_setfam_1(X0,X5) = X3
                  & v1_finset_1(X5)
                  & r1_tarski(X5,X1)
                  & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X0))) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( k8_setfam_1(X0,X7) != X6
                    | ~ v1_finset_1(X7)
                    | ~ r1_tarski(X7,X1)
                    | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )
              & ( ? [X8] :
                    ( k8_setfam_1(X0,X8) = X6
                    & v1_finset_1(X8)
                    & r1_tarski(X8,X1)
                    & m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k8_setfam_1(X0,X8) = X6
          & v1_finset_1(X8)
          & r1_tarski(X8,X1)
          & m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( k8_setfam_1(X0,sK5(X0,X1,X6)) = X6
        & v1_finset_1(sK5(X0,X1,X6))
        & r1_tarski(sK5(X0,X1,X6),X1)
        & m1_subset_1(sK5(X0,X1,X6),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k8_setfam_1(X0,X5) = X3
          & v1_finset_1(X5)
          & r1_tarski(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( k8_setfam_1(X0,sK4(X0,X1,X2)) = X3
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k8_setfam_1(X0,X4) != X3
                | ~ v1_finset_1(X4)
                | ~ r1_tarski(X4,X1)
                | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k8_setfam_1(X0,X5) = X3
                & v1_finset_1(X5)
                & r1_tarski(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X0))) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ! [X4] :
              ( k8_setfam_1(X0,X4) != sK3(X0,X1,X2)
              | ~ v1_finset_1(X4)
              | ~ r1_tarski(X4,X1)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k8_setfam_1(X0,X5) = sK3(X0,X1,X2)
              & v1_finset_1(X5)
              & r1_tarski(X5,X1)
              & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X0))) )
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( k8_setfam_1(X0,X4) != sK3(X0,X1,X2)
                | ~ v1_finset_1(X4)
                | ~ r1_tarski(X4,X1)
                | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( k8_setfam_1(X0,sK4(X0,X1,X2)) = sK3(X0,X1,X2)
              & v1_finset_1(sK4(X0,X1,X2))
              & r1_tarski(sK4(X0,X1,X2),X1)
              & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X0))) )
            | r2_hidden(sK3(X0,X1,X2),X2) )
          & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X0)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( k8_setfam_1(X0,X7) != X6
                    | ~ v1_finset_1(X7)
                    | ~ r1_tarski(X7,X1)
                    | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )
              & ( ( k8_setfam_1(X0,sK5(X0,X1,X6)) = X6
                  & v1_finset_1(sK5(X0,X1,X6))
                  & r1_tarski(sK5(X0,X1,X6),X1)
                  & m1_subset_1(sK5(X0,X1,X6),k1_zfmisc_1(k1_zfmisc_1(X0))) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,k1_zfmisc_1(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f48,f47,f46])).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
           => v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
             => v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
             => v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),sK8),X0)
        & v2_tops_2(sK8,X0)
        & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0)
            & v2_tops_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK7),X1),sK7)
          & v2_tops_2(X1,sK7)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7)
    & v2_tops_2(sK8,sK7)
    & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f33,f54,f53])).

fof(f90,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( k8_setfam_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X6),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k8_setfam_1(X0,X7) != X6
      | ~ v1_finset_1(X7)
      | ~ r1_tarski(X7,X1)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k8_setfam_1(X0,X7),X2)
      | ~ v1_finset_1(X7)
      | ~ r1_tarski(X7,X1)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k8_setfam_1(X0,X7),k1_zfmisc_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_finset_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_tarski(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    v2_tops_2(sK8,sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK6(X0,X1),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ( ~ v4_pre_topc(sK6(X0,X1),X0)
            & r2_hidden(sK6(X0,X1),X1)
            & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f51])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(sK6(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f79,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_20,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8,plain,
    ( ~ sP1(k2_cantor_1(X0,X1),X1,X0)
    | sP0(X0,X1,k2_cantor_1(X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_554,plain,
    ( sP0(X0,X1,k2_cantor_1(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | X0 != X3
    | X1 != X2
    | k2_cantor_1(X0,X1) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_8])).

cnf(c_555,plain,
    ( sP0(X0,X1,k2_cantor_1(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k2_cantor_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_565,plain,
    ( sP0(X0,X1,k2_cantor_1(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_555,c_21])).

cnf(c_8277,plain,
    ( sP0(X0,X1,k2_cantor_1(X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(sK5(X0,X1,X3),X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_8289,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(sK5(X0,X1,X3),X1) = iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12196,plain,
    ( r1_tarski(sK5(X0,X1,X2),X1) = iProver_top
    | r2_hidden(X2,k2_cantor_1(X0,X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8277,c_8289])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10088,plain,
    ( ~ r2_hidden(X0,k2_cantor_1(X1,X2))
    | m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(resolution,[status(thm)],[c_21,c_30])).

cnf(c_16819,plain,
    ( r1_tarski(sK5(X0,X1,X2),X1)
    | ~ r2_hidden(X2,k2_cantor_1(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(resolution,[status(thm)],[c_18,c_565])).

cnf(c_21861,plain,
    ( r1_tarski(sK5(X0,X1,X2),X1)
    | ~ r2_hidden(X2,k2_cantor_1(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10088,c_16819])).

cnf(c_21867,plain,
    ( r1_tarski(sK5(X0,X1,X2),X1) = iProver_top
    | r2_hidden(X2,k2_cantor_1(X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21861])).

cnf(c_35305,plain,
    ( r2_hidden(X2,k2_cantor_1(X0,X1)) != iProver_top
    | r1_tarski(sK5(X0,X1,X2),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12196,c_21867])).

cnf(c_35306,plain,
    ( r1_tarski(sK5(X0,X1,X2),X1) = iProver_top
    | r2_hidden(X2,k2_cantor_1(X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_35305])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_8279,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k2_cantor_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_672,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_35])).

cnf(c_673,plain,
    ( r2_hidden(sK2(sK7,X0),X0)
    | v2_tops_2(X0,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_8272,plain,
    ( r2_hidden(sK2(sK7,X0),X0) = iProver_top
    | v2_tops_2(X0,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_9789,plain,
    ( r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),X0)),k2_cantor_1(u1_struct_0(sK7),X0)) = iProver_top
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK7),X0),sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8287,c_8272])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
    | k8_setfam_1(X0,sK5(X0,X1,X3)) = X3 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8291,plain,
    ( k8_setfam_1(X0,sK5(X0,X1,X2)) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12203,plain,
    ( k8_setfam_1(X0,sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_cantor_1(X0,X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8277,c_8291])).

cnf(c_17055,plain,
    ( ~ r2_hidden(X0,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k8_setfam_1(X1,sK5(X1,X2,X0)) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_565])).

cnf(c_21859,plain,
    ( ~ r2_hidden(X0,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k8_setfam_1(X1,sK5(X1,X2,X0)) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10088,c_17055])).

cnf(c_21873,plain,
    ( k8_setfam_1(X0,sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_cantor_1(X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21859])).

cnf(c_35443,plain,
    ( r2_hidden(X2,k2_cantor_1(X0,X1)) != iProver_top
    | k8_setfam_1(X0,sK5(X0,X1,X2)) = X2
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12203,c_21873])).

cnf(c_35444,plain,
    ( k8_setfam_1(X0,sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_cantor_1(X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_35443])).

cnf(c_35460,plain,
    ( k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),X0,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),X0)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),X0))
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK7),X0),sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9789,c_35444])).

cnf(c_63909,plain,
    ( k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8279,c_35460])).

cnf(c_32,negated_conjecture,
    ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_702,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_35])).

cnf(c_703,plain,
    ( v2_tops_2(X0,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | m1_subset_1(sK2(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | m1_subset_1(sK2(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | k2_cantor_1(u1_struct_0(sK7),sK8) != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_703])).

cnf(c_766,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_785,plain,
    ( r2_hidden(sK2(sK7,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | k2_cantor_1(u1_struct_0(sK7),sK8) != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_673])).

cnf(c_786,plain,
    ( r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_8604,plain,
    ( m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_8638,plain,
    ( sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_9050,plain,
    ( ~ sP0(X0,X1,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(X0))
    | k8_setfam_1(X0,sK5(X0,X1,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_11376,plain,
    ( ~ sP0(u1_struct_0(sK7),X0,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7)))
    | k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),X0,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_9050])).

cnf(c_13956,plain,
    ( ~ sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7)))
    | k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_11376])).

cnf(c_64395,plain,
    ( k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63909,c_34,c_766,c_786,c_8604,c_8638,c_13956])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
    | m1_subset_1(sK5(X0,X1,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8288,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11806,plain,
    ( r2_hidden(X0,k2_cantor_1(X1,X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(sK5(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8277,c_8288])).

cnf(c_16830,plain,
    ( ~ r2_hidden(X0,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(sK5(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(resolution,[status(thm)],[c_19,c_565])).

cnf(c_21862,plain,
    ( ~ r2_hidden(X0,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(sK5(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10088,c_16830])).

cnf(c_21864,plain,
    ( r2_hidden(X0,k2_cantor_1(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(sK5(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21862])).

cnf(c_39044,plain,
    ( r2_hidden(X0,k2_cantor_1(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(sK5(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11806,c_21864])).

cnf(c_8283,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10031,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8279,c_8283])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r1_tarski(X3,X1)
    | r2_hidden(k8_setfam_1(X0,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(k8_setfam_1(X0,X3),k1_zfmisc_1(X0))
    | ~ v1_finset_1(X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_8292,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(X3,X1) != iProver_top
    | r2_hidden(k8_setfam_1(X0,X3),X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | m1_subset_1(k8_setfam_1(X0,X3),k1_zfmisc_1(X0)) != iProver_top
    | v1_finset_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12827,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r2_hidden(k8_setfam_1(u1_struct_0(sK7),X2),X1) = iProver_top
    | r2_hidden(k8_setfam_1(u1_struct_0(sK7),X2),sK8) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | v1_finset_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10031,c_8292])).

cnf(c_39077,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) != iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),X2,X3),X0) != iProver_top
    | r2_hidden(X3,k2_cantor_1(u1_struct_0(sK7),X2)) != iProver_top
    | r2_hidden(k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),X2,X3)),X1) = iProver_top
    | r2_hidden(k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),X2,X3)),sK8) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | v1_finset_1(sK5(u1_struct_0(sK7),X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_39044,c_12827])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
    | v1_finset_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8290,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
    | v1_finset_1(sK5(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11977,plain,
    ( r2_hidden(X0,k2_cantor_1(X1,X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_finset_1(sK5(X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8277,c_8290])).

cnf(c_16808,plain,
    ( ~ r2_hidden(X0,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_finset_1(sK5(X1,X2,X0)) ),
    inference(resolution,[status(thm)],[c_17,c_565])).

cnf(c_21860,plain,
    ( ~ r2_hidden(X0,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_finset_1(sK5(X1,X2,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10088,c_16808])).

cnf(c_21870,plain,
    ( r2_hidden(X0,k2_cantor_1(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_finset_1(sK5(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21860])).

cnf(c_29035,plain,
    ( r2_hidden(X0,k2_cantor_1(X1,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_finset_1(sK5(X1,X2,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11977,c_21870])).

cnf(c_42355,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) != iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),X2,X3),X0) != iProver_top
    | r2_hidden(X3,k2_cantor_1(u1_struct_0(sK7),X2)) != iProver_top
    | r2_hidden(k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),X2,X3)),X1) = iProver_top
    | r2_hidden(k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),X2,X3)),sK8) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_39077,c_29035])).

cnf(c_64401,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) != iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),X0) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),sK8) != iProver_top
    | r2_hidden(k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))),X1) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_64395,c_42355])).

cnf(c_64408,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) != iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),X0) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),X1) = iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),sK8) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_64401,c_64395])).

cnf(c_39,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_767,plain,
    ( m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_787,plain,
    ( r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8)) = iProver_top
    | m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_8605,plain,
    ( m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8604])).

cnf(c_8639,plain,
    ( sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8638])).

cnf(c_9053,plain,
    ( ~ sP0(X0,X1,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(X0))
    | v1_finset_1(sK5(X0,X1,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_11307,plain,
    ( ~ sP0(u1_struct_0(sK7),X0,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7)))
    | v1_finset_1(sK5(u1_struct_0(sK7),X0,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) ),
    inference(instantiation,[status(thm)],[c_9053])).

cnf(c_13944,plain,
    ( ~ sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7)))
    | v1_finset_1(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) ),
    inference(instantiation,[status(thm)],[c_11307])).

cnf(c_13945,plain,
    ( sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_finset_1(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13944])).

cnf(c_9051,plain,
    ( ~ sP0(X0,X1,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | m1_subset_1(sK5(X0,X1,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),k1_zfmisc_1(k1_zfmisc_1(X0)))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_11381,plain,
    ( ~ sP0(u1_struct_0(sK7),X0,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | m1_subset_1(sK5(u1_struct_0(sK7),X0,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_9051])).

cnf(c_13968,plain,
    ( ~ sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8))
    | ~ r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8))
    | m1_subset_1(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_11381])).

cnf(c_13969,plain,
    ( sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | m1_subset_1(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
    | m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13968])).

cnf(c_64399,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) != iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),X0) != iProver_top
    | r2_hidden(k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))),X1) = iProver_top
    | m1_subset_1(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_finset_1(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_64395,c_8292])).

cnf(c_64434,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) != iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),X0) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),X1) = iProver_top
    | m1_subset_1(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_finset_1(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_64399,c_64395])).

cnf(c_64466,plain,
    ( r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),X1) = iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),X0) != iProver_top
    | sP0(u1_struct_0(sK7),X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_64408,c_39,c_767,c_787,c_8605,c_8639,c_13945,c_13969,c_64434])).

cnf(c_64467,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) != iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))),X0) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_64466])).

cnf(c_64475,plain,
    ( sP0(u1_struct_0(sK7),sK8,X0) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),X0) = iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_35306,c_64467])).

cnf(c_64762,plain,
    ( sP0(u1_struct_0(sK7),sK8,X0) != iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_64475,c_39,c_787,c_8605])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK3(X0,X1,X2),X2)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8294,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK3(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10975,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),X0,X1),X1) = iProver_top
    | r2_hidden(sK2(sK7,sK4(u1_struct_0(sK7),X0,X1)),sK4(u1_struct_0(sK7),X0,X1)) = iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),X0,X1),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8294,c_8272])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2)
    | r1_tarski(sK4(X0,X1,X2),X1)
    | r2_hidden(sK3(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8295,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r1_tarski(sK4(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK3(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8285,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10030,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8285,c_8283])).

cnf(c_14275,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(X3,sK4(X0,X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X3,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8295,c_10030])).

cnf(c_25947,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),X0,X1),X1) = iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),X0,X1),sK7) = iProver_top
    | m1_subset_1(sK2(sK7,sK4(u1_struct_0(sK7),X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10975,c_14275])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8286,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_50607,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),X0,X1),X1) = iProver_top
    | r2_hidden(sK2(sK7,sK4(u1_struct_0(sK7),X0,X1)),X0) = iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),X0,X1),sK7) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_25947,c_8286])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_8282,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9964,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8285,c_8282])).

cnf(c_14123,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(X3,sK4(X0,X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X1,X2),X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8295,c_9964])).

cnf(c_25814,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),X0,X1),X1) = iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),X0,X1),sK7) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10975,c_14123])).

cnf(c_133777,plain,
    ( v2_tops_2(sK4(u1_struct_0(sK7),X0,X1),sK7) = iProver_top
    | r2_hidden(sK2(sK7,sK4(u1_struct_0(sK7),X0,X1)),X0) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),X0,X1),X1) = iProver_top
    | sP0(u1_struct_0(sK7),X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50607,c_25814])).

cnf(c_133778,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),X0,X1),X1) = iProver_top
    | r2_hidden(sK2(sK7,sK4(u1_struct_0(sK7),X0,X1)),X0) = iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),X0,X1),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_133777])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_717,plain,
    ( ~ r2_hidden(X0,X1)
    | v4_pre_topc(X0,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_35])).

cnf(c_718,plain,
    ( ~ r2_hidden(X0,X1)
    | v4_pre_topc(X0,sK7)
    | ~ v2_tops_2(X1,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_732,plain,
    ( ~ r2_hidden(X0,X1)
    | v4_pre_topc(X0,sK7)
    | ~ v2_tops_2(X1,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_718,c_30])).

cnf(c_8269,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v4_pre_topc(X0,sK7) = iProver_top
    | v2_tops_2(X1,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_8741,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v4_pre_topc(X0,sK7) = iProver_top
    | v2_tops_2(sK8,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8279,c_8269])).

cnf(c_33,negated_conjecture,
    ( v2_tops_2(sK8,sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_795,plain,
    ( ~ r2_hidden(X0,X1)
    | v4_pre_topc(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | sK8 != X1
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_732])).

cnf(c_796,plain,
    ( ~ r2_hidden(X0,sK8)
    | v4_pre_topc(X0,sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_797,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v4_pre_topc(X0,sK7) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_9231,plain,
    ( v4_pre_topc(X0,sK7) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8741,c_39,c_797])).

cnf(c_9232,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v4_pre_topc(X0,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_9231])).

cnf(c_133789,plain,
    ( sP0(u1_struct_0(sK7),sK8,X0) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),sK8,X0),X0) = iProver_top
    | v4_pre_topc(sK2(sK7,sK4(u1_struct_0(sK7),sK8,X0)),sK7) = iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),sK8,X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_133778,c_9232])).

cnf(c_2,plain,
    ( ~ v4_pre_topc(sK2(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_687,plain,
    ( ~ v4_pre_topc(sK2(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_35])).

cnf(c_688,plain,
    ( ~ v4_pre_topc(sK2(sK7,X0),sK7)
    | v2_tops_2(X0,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_8271,plain,
    ( v4_pre_topc(sK2(sK7,X0),sK7) != iProver_top
    | v2_tops_2(X0,sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_10977,plain,
    ( sP0(u1_struct_0(sK7),X0,X1) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),X0,X1),X1) = iProver_top
    | v4_pre_topc(sK2(sK7,sK4(u1_struct_0(sK7),X0,X1)),sK7) != iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),X0,X1),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8294,c_8271])).

cnf(c_138041,plain,
    ( sP0(u1_struct_0(sK7),sK8,X0) = iProver_top
    | r2_hidden(sK3(u1_struct_0(sK7),sK8,X0),X0) = iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),sK8,X0),sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_133789,c_10977])).

cnf(c_29047,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | v1_finset_1(sK5(u1_struct_0(sK7),sK8,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8279,c_29035])).

cnf(c_138050,plain,
    ( sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)) = iProver_top
    | v2_tops_2(sK4(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)),sK7) = iProver_top
    | v1_finset_1(sK5(u1_struct_0(sK7),sK8,sK3(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_138041,c_29047])).

cnf(c_139285,plain,
    ( sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_138050,c_39,c_8639])).

cnf(c_139294,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK5(u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_139285,c_8288])).

cnf(c_10029,plain,
    ( r2_hidden(X0,k2_cantor_1(X1,X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8287,c_8283])).

cnf(c_16741,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8279,c_10029])).

cnf(c_144069,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | m1_subset_1(sK5(u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_139294,c_16741])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8299,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_144081,plain,
    ( sK5(u1_struct_0(sK7),sK8,X0) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,X0)) = k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,X0))
    | r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_144069,c_8299])).

cnf(c_145889,plain,
    ( sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))))
    | sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_64762,c_144081])).

cnf(c_145905,plain,
    ( sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))
    | sP0(u1_struct_0(sK7),sK8,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_145889,c_64395])).

cnf(c_145871,plain,
    ( sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = k8_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))))
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9789,c_144081])).

cnf(c_146084,plain,
    ( sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_145871,c_64395])).

cnf(c_146343,plain,
    ( v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_146084])).

cnf(c_146446,plain,
    ( k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))
    | sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_145905,c_34,c_32,c_146343])).

cnf(c_146447,plain,
    ( sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0
    | k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)))) = sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)) ),
    inference(renaming,[status(thm)],[c_146446])).

cnf(c_28,plain,
    ( r2_hidden(sK6(X0,X1),X1)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_600,plain,
    ( r2_hidden(sK6(X0,X1),X1)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_601,plain,
    ( r2_hidden(sK6(sK7,X0),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),X0),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),X0),sK7)
    | r2_hidden(sK6(sK7,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_601,c_35])).

cnf(c_606,plain,
    ( r2_hidden(sK6(sK7,X0),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),X0),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(renaming,[status(thm)],[c_605])).

cnf(c_8275,plain,
    ( r2_hidden(sK6(sK7,X0),X0) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),X0),sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_144102,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | r2_hidden(sK6(sK7,sK5(u1_struct_0(sK7),sK8,X0)),sK5(u1_struct_0(sK7),sK8,X0)) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_144069,c_8275])).

cnf(c_10200,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10031,c_8282])).

cnf(c_144717,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | r2_hidden(sK5(u1_struct_0(sK7),sK8,X0),sK8) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,X0)),sK7) = iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_144102,c_10200])).

cnf(c_27,plain,
    ( ~ v4_pre_topc(sK6(X0,X1),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_621,plain,
    ( ~ v4_pre_topc(sK6(X0,X1),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_622,plain,
    ( ~ v4_pre_topc(sK6(sK7,X0),sK7)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),X0),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),X0),sK7)
    | ~ v4_pre_topc(sK6(sK7,X0),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_35])).

cnf(c_627,plain,
    ( ~ v4_pre_topc(sK6(sK7,X0),sK7)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),X0),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(renaming,[status(thm)],[c_626])).

cnf(c_8274,plain,
    ( v4_pre_topc(sK6(sK7,X0),sK7) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),X0),sK7) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_144104,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | v4_pre_topc(sK6(sK7,sK5(u1_struct_0(sK7),sK8,X0)),sK7) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_144069,c_8274])).

cnf(c_144094,plain,
    ( r2_hidden(X0,sK5(u1_struct_0(sK7),sK8,X1)) != iProver_top
    | r2_hidden(X1,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | v4_pre_topc(X0,sK7) = iProver_top
    | v2_tops_2(sK5(u1_struct_0(sK7),sK8,X1),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_144069,c_8269])).

cnf(c_8687,plain,
    ( ~ r2_hidden(X0,sK8)
    | v4_pre_topc(X0,sK7)
    | ~ v2_tops_2(sK8,sK7) ),
    inference(resolution,[status(thm)],[c_732,c_34])).

cnf(c_8704,plain,
    ( v4_pre_topc(X0,sK7)
    | ~ r2_hidden(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8687,c_34,c_796])).

cnf(c_8705,plain,
    ( ~ r2_hidden(X0,sK8)
    | v4_pre_topc(X0,sK7) ),
    inference(renaming,[status(thm)],[c_8704])).

cnf(c_8919,plain,
    ( v4_pre_topc(X0,sK7)
    | ~ m1_subset_1(X0,sK8)
    | v1_xboole_0(sK8) ),
    inference(resolution,[status(thm)],[c_24,c_8705])).

cnf(c_8920,plain,
    ( v4_pre_topc(X0,sK7) = iProver_top
    | m1_subset_1(X0,sK8) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8919])).

cnf(c_139292,plain,
    ( r1_tarski(sK5(u1_struct_0(sK7),sK8,X0),sK8) = iProver_top
    | r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_139285,c_8289])).

cnf(c_143489,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | r1_tarski(sK5(u1_struct_0(sK7),sK8,X0),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_139292,c_16741])).

cnf(c_143490,plain,
    ( r1_tarski(sK5(u1_struct_0(sK7),sK8,X0),sK8) = iProver_top
    | r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_143489])).

cnf(c_143497,plain,
    ( r2_hidden(X0,sK5(u1_struct_0(sK7),sK8,X1)) != iProver_top
    | r2_hidden(X1,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | m1_subset_1(X0,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_143490,c_10030])).

cnf(c_143498,plain,
    ( r2_hidden(X0,sK5(u1_struct_0(sK7),sK8,X1)) != iProver_top
    | r2_hidden(X1,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_143490,c_9964])).

cnf(c_146781,plain,
    ( v4_pre_topc(X0,sK7) = iProver_top
    | r2_hidden(X1,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | r2_hidden(X0,sK5(u1_struct_0(sK7),sK8,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_144094,c_8920,c_143497,c_143498])).

cnf(c_146782,plain,
    ( r2_hidden(X0,sK5(u1_struct_0(sK7),sK8,X1)) != iProver_top
    | r2_hidden(X1,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | v4_pre_topc(X0,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_146781])).

cnf(c_146827,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | v4_pre_topc(sK6(sK7,sK5(u1_struct_0(sK7),sK8,X0)),sK7) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_144102,c_146782])).

cnf(c_159658,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,X0)),sK7) = iProver_top
    | r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_144717,c_144104,c_146827])).

cnf(c_159659,plain,
    ( r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK7),sK5(u1_struct_0(sK7),sK8,X0)),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_159658])).

cnf(c_159666,plain,
    ( sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top
    | v4_pre_topc(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_146447,c_159659])).

cnf(c_775,plain,
    ( ~ v4_pre_topc(sK2(sK7,X0),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | k2_cantor_1(u1_struct_0(sK7),sK8) != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_688])).

cnf(c_776,plain,
    ( ~ v4_pre_topc(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),sK7)
    | ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_777,plain,
    ( v4_pre_topc(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),sK7) != iProver_top
    | m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_187362,plain,
    ( sK5(u1_struct_0(sK7),sK8,sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_159666,c_39,c_777,c_787,c_8605])).

cnf(c_187368,plain,
    ( sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)) = k8_setfam_1(u1_struct_0(sK7),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_187362,c_64395])).

cnf(c_8874,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v4_pre_topc(sK2(sK7,X0),sK7) != iProver_top
    | v2_tops_2(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8285,c_8271])).

cnf(c_188027,plain,
    ( r1_tarski(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v4_pre_topc(k8_setfam_1(u1_struct_0(sK7),k1_xboole_0),sK7) != iProver_top
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_187368,c_8874])).

cnf(c_26,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_8284,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_144085,plain,
    ( r1_tarski(sK5(u1_struct_0(sK7),sK8,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | r2_hidden(X0,k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_144069,c_8284])).

cnf(c_187417,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | r2_hidden(sK2(sK7,k2_cantor_1(u1_struct_0(sK7),sK8)),k2_cantor_1(u1_struct_0(sK7),sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_187362,c_144085])).

cnf(c_7468,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_13909,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(sK7),X2)
    | X1 != X2
    | X0 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7468])).

cnf(c_123536,plain,
    ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK7),k1_xboole_0),X0)
    | ~ v4_pre_topc(u1_struct_0(sK7),X1)
    | X0 != X1
    | k8_setfam_1(u1_struct_0(sK7),k1_xboole_0) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_13909])).

cnf(c_123549,plain,
    ( X0 != X1
    | k8_setfam_1(u1_struct_0(sK7),k1_xboole_0) != u1_struct_0(sK7)
    | v4_pre_topc(k8_setfam_1(u1_struct_0(sK7),k1_xboole_0),X0) = iProver_top
    | v4_pre_topc(u1_struct_0(sK7),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123536])).

cnf(c_123551,plain,
    ( k8_setfam_1(u1_struct_0(sK7),k1_xboole_0) != u1_struct_0(sK7)
    | sK7 != sK7
    | v4_pre_topc(k8_setfam_1(u1_struct_0(sK7),k1_xboole_0),sK7) = iProver_top
    | v4_pre_topc(u1_struct_0(sK7),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_123549])).

cnf(c_0,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_78178,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | k8_setfam_1(u1_struct_0(sK7),k1_xboole_0) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_78179,plain,
    ( k8_setfam_1(u1_struct_0(sK7),k1_xboole_0) = u1_struct_0(sK7)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78178])).

cnf(c_66911,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_66912,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66911])).

cnf(c_8801,plain,
    ( r1_tarski(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_8802,plain,
    ( r1_tarski(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | m1_subset_1(k2_cantor_1(u1_struct_0(sK7),sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8801])).

cnf(c_23,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_642,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_36])).

cnf(c_643,plain,
    ( v4_pre_topc(k2_struct_0(sK7),sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_67,plain,
    ( v4_pre_topc(k2_struct_0(sK7),sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_645,plain,
    ( v4_pre_topc(k2_struct_0(sK7),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_36,c_35,c_67])).

cnf(c_8273,plain,
    ( v4_pre_topc(k2_struct_0(sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_22,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_503,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_22,c_6])).

cnf(c_667,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_503,c_35])).

cnf(c_668,plain,
    ( k2_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_8305,plain,
    ( v4_pre_topc(u1_struct_0(sK7),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8273,c_668])).

cnf(c_7460,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7493,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_7460])).

cnf(c_41,plain,
    ( v2_tops_2(k2_cantor_1(u1_struct_0(sK7),sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_188027,c_187417,c_123551,c_78179,c_66912,c_8802,c_8605,c_8305,c_7493,c_787,c_41,c_39])).


%------------------------------------------------------------------------------
