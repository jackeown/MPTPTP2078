%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1313+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:26 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  132 (1250 expanded)
%              Number of clauses        :   86 ( 338 expanded)
%              Number of leaves         :   13 ( 373 expanded)
%              Depth                    :   21
%              Number of atoms          :  614 (10033 expanded)
%              Number of equality atoms :  162 (1881 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( v3_pre_topc(X2,X1)
                <=> ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,X1)
              <~> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK8,k2_struct_0(X1)) = X2
        & v3_pre_topc(sK8,X0)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v3_pre_topc(X2,X1) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | v3_pre_topc(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK7
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_pre_topc(sK7,X1) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK7
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | v3_pre_topc(sK7,X1) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(sK6),X3,k2_struct_0(sK6)) != X2
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v3_pre_topc(X2,sK6) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(sK6),X4,k2_struct_0(sK6)) = X2
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | v3_pre_topc(X2,sK6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
        & m1_pre_topc(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v3_pre_topc(X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,sK5)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,sK5)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK5))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,sK5) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK6),X3,k2_struct_0(sK6)) != sK7
          | ~ v3_pre_topc(X3,sK5)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
      | ~ v3_pre_topc(sK7,sK6) )
    & ( ( k9_subset_1(u1_struct_0(sK6),sK8,k2_struct_0(sK6)) = sK7
        & v3_pre_topc(sK8,sK5)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) )
      | v3_pre_topc(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_pre_topc(sK6,sK5)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f24,f28,f27,f26,f25])).

fof(f51,plain,
    ( k9_subset_1(u1_struct_0(sK6),sK8,k2_struct_0(sK6)) = sK7
    | v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1)
              & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f7,f11,f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK6),X3,k2_struct_0(sK6)) != sK7
      | ~ v3_pre_topc(X3,sK5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v3_pre_topc(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f49,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,
    ( v3_pre_topc(sK8,sK5)
    | v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK7,sK6)
    | k9_subset_1(u1_struct_0(sK6),sK8,k2_struct_0(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_593,negated_conjecture,
    ( v3_pre_topc(sK7,sK6)
    | k9_subset_1(u1_struct_0(sK6),sK8,k2_struct_0(sK6)) = sK7 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_854,plain,
    ( k9_subset_1(u1_struct_0(sK6),sK8,k2_struct_0(sK6)) = sK7
    | v3_pre_topc(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_590,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_857,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_313,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_314,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_316,plain,
    ( l1_pre_topc(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_22])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_316])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0,u1_pre_topc(sK6))
    | ~ v3_pre_topc(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0_48,u1_pre_topc(sK6))
    | ~ v3_pre_topc(X0_48,sK6) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_860,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0_48,u1_pre_topc(sK6)) = iProver_top
    | v3_pre_topc(X0_48,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_1145,plain,
    ( r2_hidden(sK7,u1_pre_topc(sK6)) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_860])).

cnf(c_25,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_621,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0_48,u1_pre_topc(sK6)) = iProver_top
    | v3_pre_topc(X0_48,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_623,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK7,u1_pre_topc(sK6)) = iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_256,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_14,c_3])).

cnf(c_260,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_256,c_15])).

cnf(c_261,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_302,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_21])).

cnf(c_303,plain,
    ( sP0(sK6,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_305,plain,
    ( sP0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_22])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK4(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | sK5 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_305])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK4(sK6,sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,u1_pre_topc(sK6)) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK4(sK6,sK5,X0_48),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_48,u1_pre_topc(sK6)) ),
    inference(subtyping,[status(esa)],[c_410])).

cnf(c_627,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK4(sK6,sK5,X0_48),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(X0_48,u1_pre_topc(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_629,plain,
    ( m1_subset_1(sK4(sK6,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK7,u1_pre_topc(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X0))
    | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(sK4(X1,X2,X0),u1_pre_topc(X2))
    | sK5 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_305])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,u1_pre_topc(sK6))
    | r2_hidden(sK4(sK6,sK5,X0),u1_pre_topc(sK5)) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_48,u1_pre_topc(sK6))
    | r2_hidden(sK4(sK6,sK5,X0_48),u1_pre_topc(sK5)) ),
    inference(subtyping,[status(esa)],[c_425])).

cnf(c_630,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0_48,u1_pre_topc(sK6)) != iProver_top
    | r2_hidden(sK4(sK6,sK5,X0_48),u1_pre_topc(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_632,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK4(sK6,sK5,sK7),u1_pre_topc(sK5)) = iProver_top
    | r2_hidden(sK7,u1_pre_topc(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X0))
    | k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X2),k2_struct_0(X0)) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | k9_subset_1(u1_struct_0(X1),sK4(X1,X2,X0),k2_struct_0(X1)) = X0
    | sK5 != X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_305])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,u1_pre_topc(sK6))
    | k9_subset_1(u1_struct_0(sK6),sK4(sK6,sK5,X0),k2_struct_0(sK6)) = X0 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_48,u1_pre_topc(sK6))
    | k9_subset_1(u1_struct_0(sK6),sK4(sK6,sK5,X0_48),k2_struct_0(sK6)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_633,plain,
    ( k9_subset_1(u1_struct_0(sK6),sK4(sK6,sK5,X0_48),k2_struct_0(sK6)) = X0_48
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0_48,u1_pre_topc(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_635,plain,
    ( k9_subset_1(u1_struct_0(sK6),sK4(sK6,sK5,sK7),k2_struct_0(sK6)) = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK7,u1_pre_topc(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,u1_pre_topc(sK5))
    | v3_pre_topc(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_48,u1_pre_topc(sK5))
    | v3_pre_topc(X0_48,sK5) ),
    inference(subtyping,[status(esa)],[c_344])).

cnf(c_1029,plain,
    ( ~ m1_subset_1(sK4(sK6,sK5,X0_48),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK4(sK6,sK5,X0_48),u1_pre_topc(sK5))
    | v3_pre_topc(sK4(sK6,sK5,X0_48),sK5) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1030,plain,
    ( m1_subset_1(sK4(sK6,sK5,X0_48),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK4(sK6,sK5,X0_48),u1_pre_topc(sK5)) != iProver_top
    | v3_pre_topc(sK4(sK6,sK5,X0_48),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_1032,plain,
    ( m1_subset_1(sK4(sK6,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK4(sK6,sK5,sK7),u1_pre_topc(sK5)) != iProver_top
    | v3_pre_topc(sK4(sK6,sK5,sK7),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X0,sK5)
    | ~ v3_pre_topc(sK7,sK6)
    | k9_subset_1(u1_struct_0(sK6),X0,k2_struct_0(sK6)) != sK7 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_594,negated_conjecture,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X0_48,sK5)
    | ~ v3_pre_topc(sK7,sK6)
    | k9_subset_1(u1_struct_0(sK6),X0_48,k2_struct_0(sK6)) != sK7 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1097,plain,
    ( ~ m1_subset_1(sK4(sK6,sK5,X0_48),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK4(sK6,sK5,X0_48),sK5)
    | ~ v3_pre_topc(sK7,sK6)
    | k9_subset_1(u1_struct_0(sK6),sK4(sK6,sK5,X0_48),k2_struct_0(sK6)) != sK7 ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_1103,plain,
    ( k9_subset_1(u1_struct_0(sK6),sK4(sK6,sK5,X0_48),k2_struct_0(sK6)) != sK7
    | m1_subset_1(sK4(sK6,sK5,X0_48),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(sK4(sK6,sK5,X0_48),sK5) != iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_1105,plain,
    ( k9_subset_1(u1_struct_0(sK6),sK4(sK6,sK5,sK7),k2_struct_0(sK6)) != sK7
    | m1_subset_1(sK4(sK6,sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(sK4(sK6,sK5,sK7),sK5) != iProver_top
    | v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_1148,plain,
    ( v3_pre_topc(sK7,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1145,c_25,c_623,c_629,c_632,c_635,c_1032,c_1105])).

cnf(c_1153,plain,
    ( k9_subset_1(u1_struct_0(sK6),sK8,k2_struct_0(sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_854,c_1148])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X0),X2,k2_struct_0(X0)),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),u1_pre_topc(X2))
    | sK5 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_305])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK6),X0,k2_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,u1_pre_topc(sK5))
    | r2_hidden(k9_subset_1(u1_struct_0(sK6),X0,k2_struct_0(sK6)),u1_pre_topc(sK6)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK6),X0_48,k2_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_48,u1_pre_topc(sK5))
    | r2_hidden(k9_subset_1(u1_struct_0(sK6),X0_48,k2_struct_0(sK6)),u1_pre_topc(sK6)) ),
    inference(subtyping,[status(esa)],[c_455])).

cnf(c_865,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK6),X0_48,k2_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0_48,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK6),X0_48,k2_struct_0(sK6)),u1_pre_topc(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_1318,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK6),sK8,k2_struct_0(sK6)),u1_pre_topc(sK6)) = iProver_top
    | r2_hidden(sK8,u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_865])).

cnf(c_1319,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK8,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(sK7,u1_pre_topc(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1318,c_1153])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_591,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(sK7,sK6) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_856,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v3_pre_topc(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X0,u1_pre_topc(sK5))
    | ~ v3_pre_topc(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X0_48,u1_pre_topc(sK5))
    | ~ v3_pre_topc(X0_48,sK5) ),
    inference(subtyping,[status(esa)],[c_329])).

cnf(c_858,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0_48,u1_pre_topc(sK5)) = iProver_top
    | v3_pre_topc(X0_48,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_1055,plain,
    ( r2_hidden(sK8,u1_pre_topc(sK5)) = iProver_top
    | v3_pre_topc(sK8,sK5) != iProver_top
    | v3_pre_topc(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_856,c_858])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(sK8,sK5)
    | v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_27,plain,
    ( v3_pre_topc(sK8,sK5) = iProver_top
    | v3_pre_topc(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1085,plain,
    ( r2_hidden(sK8,u1_pre_topc(sK5)) = iProver_top
    | v3_pre_topc(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1055,c_27])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_316])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,u1_pre_topc(sK6))
    | v3_pre_topc(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_48,u1_pre_topc(sK6))
    | v3_pre_topc(X0_48,sK6) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_624,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0_48,u1_pre_topc(sK6)) != iProver_top
    | v3_pre_topc(X0_48,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_626,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK7,u1_pre_topc(sK6)) != iProver_top
    | v3_pre_topc(sK7,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_26,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v3_pre_topc(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1319,c_1148,c_1085,c_626,c_26,c_25])).


%------------------------------------------------------------------------------
