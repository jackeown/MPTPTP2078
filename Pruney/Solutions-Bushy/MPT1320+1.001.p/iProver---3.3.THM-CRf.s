%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1320+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:28 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 141 expanded)
%              Number of clauses        :   31 (  33 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  378 ( 853 expanded)
%              Number of equality atoms :   43 (  45 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                 => ( r2_hidden(X1,X3)
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ( r2_hidden(X1,X3)
                     => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,sK8))
        & r2_hidden(X1,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
              & r2_hidden(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,sK7),k1_tops_2(X0,sK7,X3))
            & r2_hidden(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6,X2),k1_tops_2(X0,X2,X3))
                & r2_hidden(sK6,X3)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),k1_tops_2(X0,X2,X3))
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X2),k1_tops_2(sK5,X2,X3))
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8))
    & r2_hidden(sK6,sK8)
    & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f11,f27,f26,f25,f24])).

fof(f43,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,plain,(
    ! [X3,X2,X0,X1] :
      ( ( k1_tops_2(X0,X1,X2) = X3
      <=> sP0(X1,X0,X2,X3) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X3,X2,X0,X1] :
      ( ( ( k1_tops_2(X0,X1,X2) = X3
          | ~ sP0(X1,X0,X2,X3) )
        & ( sP0(X1,X0,X2,X3)
          | k1_tops_2(X0,X1,X2) != X3 ) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_tops_2(X2,X3,X1) = X0
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k1_tops_2(X2,X3,X1) != X0 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k1_tops_2(X2,X3,X1) != X0
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X3,X1] :
      ( sP0(X3,X2,X1,k1_tops_2(X2,X3,X1))
      | ~ sP1(k1_tops_2(X2,X3,X1),X1,X2,X3) ) ),
    inference(equality_resolution,[],[f29])).

fof(f1,axiom,(
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

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
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

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X3,X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f6,f13,f12])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( k9_subset_1(u1_struct_0(X1),X9,X0) = X7
          & r2_hidden(X9,X2)
          & m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X7),X0) = X7
        & r2_hidden(sK4(X0,X1,X2,X7),X2)
        & m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( k9_subset_1(u1_struct_0(X1),X6,X0) = X4
          & r2_hidden(X6,X2)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2,X3),X0) = X4
        & r2_hidden(sK3(X0,X1,X2,X3),X2)
        & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
              ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK2(X0,X1,X2,X3)
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( k9_subset_1(u1_struct_0(X1),X6,X0) = sK2(X0,X1,X2,X3)
              & r2_hidden(X6,X2)
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( k9_subset_1(u1_struct_0(X1),X5,X0) != sK2(X0,X1,X2,X3)
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( ( k9_subset_1(u1_struct_0(X1),sK3(X0,X1,X2,X3),X0) = sK2(X0,X1,X2,X3)
              & r2_hidden(sK3(X0,X1,X2,X3),X2)
              & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) ) )
      & ( ! [X7] :
            ( ( ( r2_hidden(X7,X3)
                | ! [X8] :
                    ( k9_subset_1(u1_struct_0(X1),X8,X0) != X7
                    | ~ r2_hidden(X8,X2)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2,X7),X0) = X7
                  & r2_hidden(sK4(X0,X1,X2,X7),X2)
                  & m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X7,X3) ) )
            | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0)))) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).

fof(f34,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | k9_subset_1(u1_struct_0(X1),X8,X0) != X7
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X1),X8,X0),X3)
      | ~ r2_hidden(X8,X2)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X8,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f34])).

fof(f48,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8)) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k9_subset_1(u1_struct_0(X1),X0,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK5),X0,X1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X1)))) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_1999,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK5),X0_45,X1_45),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X1_45)))) ),
    inference(subtyping,[status(esa)],[c_241])).

cnf(c_2955,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK5),sK6,X0_45),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X0_45))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_3190,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,sK7))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2955])).

cnf(c_1,plain,
    ( ~ sP1(k1_tops_2(X0,X1,X2),X2,X0,X1)
    | sP0(X1,X0,X2,k1_tops_2(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_222,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_223,plain,
    ( sP1(X0,X1,sK5,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X2)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_304,plain,
    ( sP0(X0,X1,X2,k1_tops_2(X1,X0,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X4)))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK5)))
    | X4 != X0
    | X5 != X2
    | k1_tops_2(X1,X0,X2) != X3
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_223])).

cnf(c_305,plain,
    ( sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k1_tops_2(sK5,X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X0))))) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_2(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_2(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_256,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(k1_tops_2(sK5,X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X1))))) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_317,plain,
    ( sP0(X0,sK5,X1,k1_tops_2(sK5,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_305,c_256])).

cnf(c_1996,plain,
    ( sP0(X0_45,sK5,X1_45,k1_tops_2(sK5,X0_45,X1_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_317])).

cnf(c_2524,plain,
    ( sP0(X0_45,sK5,sK8,k1_tops_2(sK5,X0_45,sK8))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_2848,plain,
    ( sP0(sK7,sK5,sK8,k1_tops_2(sK5,sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X4,X0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ r2_hidden(X4,X2)
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X4,X0),X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2008,plain,
    ( ~ sP0(X0_45,X0_46,X1_45,X2_45)
    | ~ m1_subset_1(X3_45,k1_zfmisc_1(u1_struct_0(X0_46)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0_46),X3_45,X0_45),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0_46,X0_45))))
    | ~ r2_hidden(X3_45,X1_45)
    | r2_hidden(k9_subset_1(u1_struct_0(X0_46),X3_45,X0_45),X2_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2582,plain,
    ( ~ sP0(X0_45,X0_46,sK8,X1_45)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0_46),sK6,X0_45),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0_46,X0_45))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0_46)))
    | r2_hidden(k9_subset_1(u1_struct_0(X0_46),sK6,X0_45),X1_45)
    | ~ r2_hidden(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_2685,plain,
    ( ~ sP0(X0_45,sK5,sK8,k1_tops_2(sK5,X0_45,sK8))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK5),sK6,X0_45),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,X0_45))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,X0_45),k1_tops_2(sK5,X0_45,sK8))
    | ~ r2_hidden(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_2582])).

cnf(c_2787,plain,
    ( ~ sP0(sK7,sK5,sK8,k1_tops_2(sK5,sK7,sK8))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,sK7))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8))
    | ~ r2_hidden(sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK6,sK7),k1_tops_2(sK5,sK7,sK8)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK6,sK8) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3190,c_2848,c_2787,c_14,c_15,c_16,c_17,c_18])).


%------------------------------------------------------------------------------
