%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1319+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:28 EST 2020

% Result     : Theorem 23.37s
% Output     : CNFRefutation 23.37s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 298 expanded)
%              Number of clauses        :   71 (  93 expanded)
%              Number of leaves         :   18 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  536 (1681 expanded)
%              Number of equality atoms :   76 ( 148 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,plain,(
    ! [X1,X0,X2,X3] :
      ( sP0(X1,X0,X2,X3)
    <=> ! [X4] :
          ( ( r2_hidden(X4,X3)
          <=> ? [X5] :
                ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                & r2_hidden(X5,X2)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP0(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                  & r2_hidden(X5,X2)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X3)
                | ! [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ? [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                    & r2_hidden(X5,X2)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X3) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
        | ~ sP0(X1,X0,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X1,X0,X2,X3] :
      ( ( sP0(X1,X0,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                  & r2_hidden(X5,X2)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X3)
                | ! [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) != X4
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & ( ? [X5] :
                    ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                    & r2_hidden(X5,X2)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X3) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
        | ~ sP0(X1,X0,X2,X3) ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( k9_subset_1(u1_struct_0(X1),X5,X0) != X4
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
                  & r2_hidden(X6,X2)
                  & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X4,X3) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) )
      & ( ! [X7] :
            ( ( ( r2_hidden(X7,X3)
                | ! [X8] :
                    ( k9_subset_1(u1_struct_0(X1),X8,X0) != X7
                    | ~ r2_hidden(X8,X2)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ? [X9] :
                    ( k9_subset_1(u1_struct_0(X1),X9,X0) = X7
                    & r2_hidden(X9,X2)
                    & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X7,X3) ) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X1),X9,X0) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,X7),X0) = X7
        & r2_hidden(sK5(X0,X1,X2,X7),X2)
        & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X3),X0) = X4
        & r2_hidden(sK4(X0,X1,X2,X3),X2)
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X1),X5,X0) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
                & r2_hidden(X6,X2)
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X4,X3) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
     => ( ( ! [X5] :
              ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK3(X0,X1,X2,X3)
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( k9_subset_1(u1_struct_0(X1),X6,X0) = sK3(X0,X1,X2,X3)
              & r2_hidden(X6,X2)
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK3(X0,X1,X2,X3)
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X3),X0) = sK3(X0,X1,X2,X3)
              & r2_hidden(sK4(X0,X1,X2,X3),X2)
              & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) )
      & ( ! [X7] :
            ( ( ( r2_hidden(X7,X3)
                | ! [X8] :
                    ( k9_subset_1(u1_struct_0(X1),X8,X0) != X7
                    | ~ r2_hidden(X8,X2)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,X7),X0) = X7
                  & r2_hidden(sK5(X0,X1,X2,X7),X2)
                  & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X7,X3) ) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f47,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,X7),X0) = X7
      | ~ r2_hidden(X7,X3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | k9_subset_1(u1_struct_0(X1),X8,X0) != X7
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X1),X8,X0),X3)
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X8,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2,X7),X2)
      | ~ r2_hidden(X7,X3)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,plain,(
    ! [X3,X2,X0,X1] :
      ( ( k1_tops_2(X0,X1,X2) = X3
      <=> sP0(X1,X0,X2,X3) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X3,X2,X0,X1] :
      ( ( ( k1_tops_2(X0,X1,X2) = X3
          | ~ sP0(X1,X0,X2,X3) )
        & ( sP0(X1,X0,X2,X3)
          | k1_tops_2(X0,X1,X2) != X3 ) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_tops_2(X2,X3,X1) = X0
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k1_tops_2(X2,X3,X1) != X0 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k1_tops_2(X2,X3,X1) != X0
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X2,X3,X1] :
      ( sP0(X3,X2,X1,k1_tops_2(X2,X3,X1))
      | ~ sP1(k1_tops_2(X2,X3,X1),X1,X2,X3) ) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X3,X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f10,f19,f18])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r1_tarski(X2,X3)
                     => r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
          & r1_tarski(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,sK9))
        & r1_tarski(X2,sK9)
        & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
              & r1_tarski(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X3] :
            ( ~ r1_tarski(k1_tops_2(X0,X1,sK8),k1_tops_2(X0,X1,X3))
            & r1_tarski(sK8,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k1_tops_2(X0,sK7,X2),k1_tops_2(X0,sK7,X3))
                & r1_tarski(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k1_tops_2(X0,X1,X2),k1_tops_2(X0,X1,X3))
                    & r1_tarski(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_tops_2(sK6,X1,X2),k1_tops_2(sK6,X1,X3))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r1_tarski(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))
    & r1_tarski(sK8,sK9)
    & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f17,f37,f36,f35,f34])).

fof(f58,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ~ r1_tarski(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6090,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_34049,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | ~ m1_subset_1(k1_tops_2(sK6,sK7,sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))))
    | ~ r2_hidden(X0,k1_tops_2(sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_6090])).

cnf(c_54852,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | ~ m1_subset_1(k1_tops_2(sK6,sK7,sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7),k1_tops_2(sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_34049])).

cnf(c_2192,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3747,plain,
    ( X0 != X1
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) != X1
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) = X0 ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_5980,plain,
    ( X0 != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) = X0
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_3747])).

cnf(c_11847,plain,
    ( k9_subset_1(u1_struct_0(X0),sK5(X1,X0,X2,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),X1) != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) = k9_subset_1(u1_struct_0(X0),sK5(X1,X0,X2,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),X1)
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_5980])).

cnf(c_40958,plain,
    ( k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7) != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) = k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7)
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_11847])).

cnf(c_2194,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3565,plain,
    ( r2_hidden(X0,k1_tops_2(sK6,sK7,sK8))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8))
    | X0 != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_4072,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X1,X0,X2,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),X1),k1_tops_2(sK6,sK7,sK8))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8))
    | k9_subset_1(u1_struct_0(X0),sK5(X1,X0,X2,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),X1) != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_3565])).

cnf(c_40959,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7),k1_tops_2(sK6,sK7,sK8))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8))
    | k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7) != sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_4072])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(X4,X3)
    | k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,X4),X0) = X4 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5919,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),X3)
    | k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),X0) = sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11575,plain,
    ( ~ sP0(X0,X1,X2,k1_tops_2(sK6,sK7,sK8))
    | ~ m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8))
    | k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),X0) = sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_5919])).

cnf(c_13491,plain,
    ( ~ sP0(sK7,sK6,X0,k1_tops_2(sK6,sK7,sK8))
    | ~ m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8))
    | k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,X0,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7) = sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_11575])).

cnf(c_18889,plain,
    ( ~ sP0(sK7,sK6,sK8,k1_tops_2(sK6,sK7,sK8))
    | ~ m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8))
    | k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7) = sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_13491])).

cnf(c_2681,plain,
    ( ~ r2_hidden(X0,k1_tops_2(sK6,sK7,sK9))
    | r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK9))
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_2936,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(sK6,sK7,sK9))
    | r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK9))
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) != k9_subset_1(u1_struct_0(X0),X1,X2) ),
    inference(instantiation,[status(thm)],[c_2681])).

cnf(c_13218,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7),k1_tops_2(sK6,sK7,sK9))
    | r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK9))
    | sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) != k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7) ),
    inference(instantiation,[status(thm)],[c_2936])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X4,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(X4,X2)
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X4,X0),X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3273,plain,
    ( ~ sP0(X0,X1,X2,k1_tops_2(sK6,sK7,sK9))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(X3,X2)
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,X0),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6725,plain,
    ( ~ sP0(X0,X1,sK9,k1_tops_2(sK6,sK7,sK9))
    | ~ m1_subset_1(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK9)
    | r2_hidden(k9_subset_1(u1_struct_0(X1),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),X0),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_3273])).

cnf(c_11264,plain,
    ( ~ sP0(sK7,sK6,sK9,k1_tops_2(sK6,sK7,sK9))
    | ~ m1_subset_1(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | ~ r2_hidden(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK9)
    | r2_hidden(k9_subset_1(u1_struct_0(sK6),sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK7),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_6725])).

cnf(c_2191,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5978,plain,
    ( sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) = sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2810,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK9)
    | ~ r1_tarski(X1,sK9) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3084,plain,
    ( r2_hidden(X0,sK9)
    | ~ r2_hidden(X0,sK8)
    | ~ r1_tarski(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2810])).

cnf(c_3368,plain,
    ( r2_hidden(sK5(X0,X1,sK8,X2),sK9)
    | ~ r2_hidden(sK5(X0,X1,sK8,X2),sK8)
    | ~ r1_tarski(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_3084])).

cnf(c_4761,plain,
    ( r2_hidden(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK9)
    | ~ r2_hidden(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK8)
    | ~ r1_tarski(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_3368])).

cnf(c_2636,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2745,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ r2_hidden(X0,sK8) ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_2838,plain,
    ( m1_subset_1(sK5(X0,X1,sK8,X2),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ r2_hidden(sK5(X0,X1,sK8,X2),sK8) ),
    inference(instantiation,[status(thm)],[c_2745])).

cnf(c_4762,plain,
    ( m1_subset_1(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ r2_hidden(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK8) ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(X4,X3)
    | r2_hidden(sK5(X0,X1,X2,X4),X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3169,plain,
    ( ~ sP0(X0,X1,sK8,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(X3,X2)
    | r2_hidden(sK5(X0,X1,sK8,X3),sK8) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3791,plain,
    ( ~ sP0(X0,X1,sK8,k1_tops_2(sK6,sK7,sK8))
    | ~ m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | r2_hidden(sK5(X0,X1,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK8)
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_3169])).

cnf(c_4156,plain,
    ( ~ sP0(sK7,sK6,sK8,k1_tops_2(sK6,sK7,sK8))
    | ~ m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | r2_hidden(sK5(sK7,sK6,sK8,sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9))),sK8)
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_3791])).

cnf(c_3453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,X1)))))
    | m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,X1))))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3645,plain,
    ( ~ m1_subset_1(k1_tops_2(sK6,sK7,sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,X0)))))
    | m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,X0))))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_3453])).

cnf(c_4080,plain,
    ( ~ m1_subset_1(k1_tops_2(sK6,sK7,sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))))
    | m1_subset_1(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_3645])).

cnf(c_5,plain,
    ( ~ sP1(k1_tops_2(X0,X1,X2),X2,X0,X1)
    | sP0(X1,X0,X2,k1_tops_2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_270,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_271,plain,
    ( sP1(X0,X1,sK6,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,X2)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_333,plain,
    ( sP0(X0,X1,X2,k1_tops_2(X1,X0,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,X4)))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
    | X4 != X0
    | X5 != X2
    | k1_tops_2(X1,X0,X2) != X3
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_271])).

cnf(c_334,plain,
    ( sP0(X0,sK6,X1,k1_tops_2(sK6,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(k1_tops_2(sK6,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,X0))))) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_2(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_2(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(k1_tops_2(sK6,X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,X1))))) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_346,plain,
    ( sP0(X0,sK6,X1,k1_tops_2(sK6,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_334,c_289])).

cnf(c_2646,plain,
    ( sP0(sK7,sK6,X0,k1_tops_2(sK6,sK7,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_2712,plain,
    ( sP0(sK7,sK6,sK8,k1_tops_2(sK6,sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_2646])).

cnf(c_2709,plain,
    ( sP0(sK7,sK6,sK9,k1_tops_2(sK6,sK7,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_2646])).

cnf(c_2626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | m1_subset_1(k1_tops_2(sK6,sK7,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_2696,plain,
    ( m1_subset_1(k1_tops_2(sK6,sK7,sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_2626])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_396,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | k1_tops_2(sK6,sK7,sK9) != X1
    | k1_tops_2(sK6,sK7,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_397,plain,
    ( ~ r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK9)) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_389,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k1_tops_2(sK6,sK7,sK9) != X1
    | k1_tops_2(sK6,sK7,sK8) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_390,plain,
    ( r2_hidden(sK2(k1_tops_2(sK6,sK7,sK8),k1_tops_2(sK6,sK7,sK9)),k1_tops_2(sK6,sK7,sK8)) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK8,sK9) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54852,c_40958,c_40959,c_18889,c_13218,c_11264,c_5978,c_4761,c_4762,c_4156,c_4080,c_2712,c_2709,c_2696,c_397,c_390,c_20,c_21,c_22,c_23])).


%------------------------------------------------------------------------------
