%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:59 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  147 (1013 expanded)
%              Number of clauses        :   90 ( 307 expanded)
%              Number of leaves         :   21 ( 287 expanded)
%              Depth                    :   23
%              Number of atoms          :  595 (7222 expanded)
%              Number of equality atoms :  152 ( 371 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( r1_tsep_1(X3,X2)
            | r1_tsep_1(X2,X3) )
          & ( ~ r1_tsep_1(X3,X1)
            | ~ r1_tsep_1(X1,X3) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0) )
     => ( ( r1_tsep_1(sK8,X2)
          | r1_tsep_1(X2,sK8) )
        & ( ~ r1_tsep_1(sK8,X1)
          | ~ r1_tsep_1(X1,sK8) )
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,X1)
                | ~ r1_tsep_1(X1,X3) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0) )
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ( r1_tsep_1(X3,sK7)
              | r1_tsep_1(sK7,X3) )
            & ( ~ r1_tsep_1(X3,X1)
              | ~ r1_tsep_1(X1,X3) )
            & m1_pre_topc(X1,sK7)
            & m1_pre_topc(X3,X0) )
        & m1_pre_topc(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,sK6)
                  | ~ r1_tsep_1(sK6,X3) )
                & m1_pre_topc(sK6,X2)
                & m1_pre_topc(X3,X0) )
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK5) )
              & m1_pre_topc(X2,sK5) )
          & m1_pre_topc(X1,sK5) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( r1_tsep_1(sK8,sK7)
      | r1_tsep_1(sK7,sK8) )
    & ( ~ r1_tsep_1(sK8,sK6)
      | ~ r1_tsep_1(sK6,sK8) )
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK8,sK5)
    & m1_pre_topc(sK7,sK5)
    & m1_pre_topc(sK6,sK5)
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f22,f39,f38,f37,f36])).

fof(f67,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f23,plain,(
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

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f15,f24,f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,
    ( r1_tsep_1(sK8,sK7)
    | r1_tsep_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ r1_tsep_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_555,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_556,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_558,plain,
    ( l1_pre_topc(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_29])).

cnf(c_626,plain,
    ( l1_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_558])).

cnf(c_627,plain,
    ( l1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_3531,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3552,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3946,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_3531,c_3552])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_577,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_578,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_580,plain,
    ( l1_pre_topc(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_29])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_534,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_535,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_588,plain,
    ( l1_pre_topc(sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_580,c_535])).

cnf(c_640,plain,
    ( l1_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_588])).

cnf(c_641,plain,
    ( l1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_3529,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_3949,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_3529,c_3552])).

cnf(c_20,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3541,plain,
    ( r1_tsep_1(X0,X1) = iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4506,plain,
    ( r1_tsep_1(sK6,X0) = iProver_top
    | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3949,c_3541])).

cnf(c_642,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_12005,plain,
    ( l1_struct_0(X0) != iProver_top
    | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) != iProver_top
    | r1_tsep_1(sK6,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4506,c_642])).

cnf(c_12006,plain,
    ( r1_tsep_1(sK6,X0) = iProver_top
    | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12005])).

cnf(c_12015,plain,
    ( r1_tsep_1(sK6,sK8) = iProver_top
    | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3946,c_12006])).

cnf(c_30,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_47,plain,
    ( l1_pre_topc(sK8) != iProver_top
    | l1_struct_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_557,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_633,plain,
    ( l1_struct_0(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_580])).

cnf(c_634,plain,
    ( l1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_635,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_396,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_17,c_6])).

cnf(c_400,plain,
    ( ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_19])).

cnf(c_401,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_400])).

cnf(c_524,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_25])).

cnf(c_525,plain,
    ( sP0(sK6,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_587,plain,
    ( sP0(sK6,sK7) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_580,c_525])).

cnf(c_1239,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
    | sK6 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_587])).

cnf(c_1240,plain,
    ( r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1239])).

cnf(c_1241,plain,
    ( r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_21,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3774,plain,
    ( ~ r1_tsep_1(sK7,sK8)
    | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3775,plain,
    ( r1_tsep_1(sK7,sK8) != iProver_top
    | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = iProver_top
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3774])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3887,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
    | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3888,plain,
    ( k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = u1_struct_0(sK7)
    | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3887])).

cnf(c_22,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3898,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3902,plain,
    ( r1_tsep_1(sK7,sK8) = iProver_top
    | r1_tsep_1(sK8,sK7) != iProver_top
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3898])).

cnf(c_3530,plain,
    ( l1_struct_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_3948,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(superposition,[status(thm)],[c_3530,c_3552])).

cnf(c_2855,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4293,plain,
    ( k2_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2855])).

cnf(c_23,negated_conjecture,
    ( r1_tsep_1(sK7,sK8)
    | r1_tsep_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3538,plain,
    ( r1_tsep_1(sK7,sK8) = iProver_top
    | r1_tsep_1(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3539,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4317,plain,
    ( r1_tsep_1(sK8,sK7) = iProver_top
    | l1_struct_0(sK7) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_3539])).

cnf(c_4581,plain,
    ( r1_tsep_1(sK6,sK8) = iProver_top
    | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4506])).

cnf(c_2856,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4029,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK7)
    | u1_struct_0(sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_2856])).

cnf(c_4202,plain,
    ( X0 = u1_struct_0(sK7)
    | X0 != k2_struct_0(sK7)
    | u1_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4029])).

cnf(c_4858,plain,
    ( u1_struct_0(sK7) != k2_struct_0(sK7)
    | k2_struct_0(sK7) = u1_struct_0(sK7)
    | k2_struct_0(sK7) != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4202])).

cnf(c_4859,plain,
    ( k2_struct_0(sK7) = k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2855])).

cnf(c_3979,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X3) != X1
    | k4_xboole_0(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_2856])).

cnf(c_4307,plain,
    ( X0 != u1_struct_0(sK7)
    | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = X0
    | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3979])).

cnf(c_5576,plain,
    ( k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != u1_struct_0(sK7)
    | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = k2_struct_0(sK7)
    | k2_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4307])).

cnf(c_2858,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4054,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
    | X0 != k2_struct_0(sK6)
    | X1 != k2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_4292,plain,
    ( r1_tarski(k2_struct_0(sK6),X0)
    | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
    | X0 != k2_struct_0(sK7)
    | k2_struct_0(sK6) != k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4054])).

cnf(c_6214,plain,
    ( r1_tarski(k2_struct_0(sK6),k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)))
    | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
    | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != k2_struct_0(sK7)
    | k2_struct_0(sK6) != k2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4292])).

cnf(c_6225,plain,
    ( k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != k2_struct_0(sK7)
    | k2_struct_0(sK6) != k2_struct_0(sK6)
    | r1_tarski(k2_struct_0(sK6),k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))) = iProver_top
    | r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6214])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7020,plain,
    ( ~ r1_tarski(k2_struct_0(sK6),k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)))
    | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7021,plain,
    ( r1_tarski(k2_struct_0(sK6),k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))) != iProver_top
    | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7020])).

cnf(c_12041,plain,
    ( r1_tsep_1(sK6,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12015,c_30,c_47,c_557,c_635,c_642,c_1241,c_3775,c_3888,c_3902,c_3948,c_4293,c_4317,c_4581,c_4858,c_4859,c_5576,c_6225,c_7021])).

cnf(c_12047,plain,
    ( r1_tsep_1(sK8,sK6) = iProver_top
    | l1_struct_0(sK6) != iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_12041,c_3539])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tsep_1(sK6,sK8)
    | ~ r1_tsep_1(sK8,sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( r1_tsep_1(sK6,sK8) != iProver_top
    | r1_tsep_1(sK8,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12047,c_7021,c_6225,c_5576,c_4859,c_4858,c_4581,c_4317,c_4293,c_3948,c_3902,c_3888,c_3775,c_1241,c_642,c_635,c_557,c_47,c_35,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:30:19 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.42/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.42/0.99  
% 3.42/0.99  ------  iProver source info
% 3.42/0.99  
% 3.42/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.42/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.42/0.99  git: non_committed_changes: false
% 3.42/0.99  git: last_make_outside_of_git: false
% 3.42/0.99  
% 3.42/0.99  ------ 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options
% 3.42/0.99  
% 3.42/0.99  --out_options                           all
% 3.42/0.99  --tptp_safe_out                         true
% 3.42/0.99  --problem_path                          ""
% 3.42/0.99  --include_path                          ""
% 3.42/0.99  --clausifier                            res/vclausify_rel
% 3.42/0.99  --clausifier_options                    --mode clausify
% 3.42/0.99  --stdin                                 false
% 3.42/0.99  --stats_out                             all
% 3.42/0.99  
% 3.42/0.99  ------ General Options
% 3.42/0.99  
% 3.42/0.99  --fof                                   false
% 3.42/0.99  --time_out_real                         305.
% 3.42/0.99  --time_out_virtual                      -1.
% 3.42/0.99  --symbol_type_check                     false
% 3.42/0.99  --clausify_out                          false
% 3.42/0.99  --sig_cnt_out                           false
% 3.42/0.99  --trig_cnt_out                          false
% 3.42/0.99  --trig_cnt_out_tolerance                1.
% 3.42/0.99  --trig_cnt_out_sk_spl                   false
% 3.42/0.99  --abstr_cl_out                          false
% 3.42/0.99  
% 3.42/0.99  ------ Global Options
% 3.42/0.99  
% 3.42/0.99  --schedule                              default
% 3.42/0.99  --add_important_lit                     false
% 3.42/0.99  --prop_solver_per_cl                    1000
% 3.42/0.99  --min_unsat_core                        false
% 3.42/0.99  --soft_assumptions                      false
% 3.42/0.99  --soft_lemma_size                       3
% 3.42/0.99  --prop_impl_unit_size                   0
% 3.42/0.99  --prop_impl_unit                        []
% 3.42/0.99  --share_sel_clauses                     true
% 3.42/0.99  --reset_solvers                         false
% 3.42/0.99  --bc_imp_inh                            [conj_cone]
% 3.42/0.99  --conj_cone_tolerance                   3.
% 3.42/0.99  --extra_neg_conj                        none
% 3.42/0.99  --large_theory_mode                     true
% 3.42/0.99  --prolific_symb_bound                   200
% 3.42/0.99  --lt_threshold                          2000
% 3.42/0.99  --clause_weak_htbl                      true
% 3.42/0.99  --gc_record_bc_elim                     false
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing Options
% 3.42/0.99  
% 3.42/0.99  --preprocessing_flag                    true
% 3.42/0.99  --time_out_prep_mult                    0.1
% 3.42/0.99  --splitting_mode                        input
% 3.42/0.99  --splitting_grd                         true
% 3.42/0.99  --splitting_cvd                         false
% 3.42/0.99  --splitting_cvd_svl                     false
% 3.42/0.99  --splitting_nvd                         32
% 3.42/0.99  --sub_typing                            true
% 3.42/0.99  --prep_gs_sim                           true
% 3.42/0.99  --prep_unflatten                        true
% 3.42/0.99  --prep_res_sim                          true
% 3.42/0.99  --prep_upred                            true
% 3.42/0.99  --prep_sem_filter                       exhaustive
% 3.42/0.99  --prep_sem_filter_out                   false
% 3.42/0.99  --pred_elim                             true
% 3.42/0.99  --res_sim_input                         true
% 3.42/0.99  --eq_ax_congr_red                       true
% 3.42/0.99  --pure_diseq_elim                       true
% 3.42/0.99  --brand_transform                       false
% 3.42/0.99  --non_eq_to_eq                          false
% 3.42/0.99  --prep_def_merge                        true
% 3.42/0.99  --prep_def_merge_prop_impl              false
% 3.42/0.99  --prep_def_merge_mbd                    true
% 3.42/0.99  --prep_def_merge_tr_red                 false
% 3.42/0.99  --prep_def_merge_tr_cl                  false
% 3.42/0.99  --smt_preprocessing                     true
% 3.42/0.99  --smt_ac_axioms                         fast
% 3.42/0.99  --preprocessed_out                      false
% 3.42/0.99  --preprocessed_stats                    false
% 3.42/0.99  
% 3.42/0.99  ------ Abstraction refinement Options
% 3.42/0.99  
% 3.42/0.99  --abstr_ref                             []
% 3.42/0.99  --abstr_ref_prep                        false
% 3.42/0.99  --abstr_ref_until_sat                   false
% 3.42/0.99  --abstr_ref_sig_restrict                funpre
% 3.42/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.99  --abstr_ref_under                       []
% 3.42/0.99  
% 3.42/0.99  ------ SAT Options
% 3.42/0.99  
% 3.42/0.99  --sat_mode                              false
% 3.42/0.99  --sat_fm_restart_options                ""
% 3.42/0.99  --sat_gr_def                            false
% 3.42/0.99  --sat_epr_types                         true
% 3.42/0.99  --sat_non_cyclic_types                  false
% 3.42/0.99  --sat_finite_models                     false
% 3.42/0.99  --sat_fm_lemmas                         false
% 3.42/0.99  --sat_fm_prep                           false
% 3.42/0.99  --sat_fm_uc_incr                        true
% 3.42/0.99  --sat_out_model                         small
% 3.42/0.99  --sat_out_clauses                       false
% 3.42/0.99  
% 3.42/0.99  ------ QBF Options
% 3.42/0.99  
% 3.42/0.99  --qbf_mode                              false
% 3.42/0.99  --qbf_elim_univ                         false
% 3.42/0.99  --qbf_dom_inst                          none
% 3.42/0.99  --qbf_dom_pre_inst                      false
% 3.42/0.99  --qbf_sk_in                             false
% 3.42/0.99  --qbf_pred_elim                         true
% 3.42/0.99  --qbf_split                             512
% 3.42/0.99  
% 3.42/0.99  ------ BMC1 Options
% 3.42/0.99  
% 3.42/0.99  --bmc1_incremental                      false
% 3.42/0.99  --bmc1_axioms                           reachable_all
% 3.42/0.99  --bmc1_min_bound                        0
% 3.42/0.99  --bmc1_max_bound                        -1
% 3.42/0.99  --bmc1_max_bound_default                -1
% 3.42/0.99  --bmc1_symbol_reachability              true
% 3.42/0.99  --bmc1_property_lemmas                  false
% 3.42/0.99  --bmc1_k_induction                      false
% 3.42/0.99  --bmc1_non_equiv_states                 false
% 3.42/0.99  --bmc1_deadlock                         false
% 3.42/0.99  --bmc1_ucm                              false
% 3.42/0.99  --bmc1_add_unsat_core                   none
% 3.42/0.99  --bmc1_unsat_core_children              false
% 3.42/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.99  --bmc1_out_stat                         full
% 3.42/0.99  --bmc1_ground_init                      false
% 3.42/0.99  --bmc1_pre_inst_next_state              false
% 3.42/0.99  --bmc1_pre_inst_state                   false
% 3.42/0.99  --bmc1_pre_inst_reach_state             false
% 3.42/0.99  --bmc1_out_unsat_core                   false
% 3.42/0.99  --bmc1_aig_witness_out                  false
% 3.42/0.99  --bmc1_verbose                          false
% 3.42/0.99  --bmc1_dump_clauses_tptp                false
% 3.42/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.99  --bmc1_dump_file                        -
% 3.42/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.99  --bmc1_ucm_extend_mode                  1
% 3.42/0.99  --bmc1_ucm_init_mode                    2
% 3.42/0.99  --bmc1_ucm_cone_mode                    none
% 3.42/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.99  --bmc1_ucm_relax_model                  4
% 3.42/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.99  --bmc1_ucm_layered_model                none
% 3.42/0.99  --bmc1_ucm_max_lemma_size               10
% 3.42/0.99  
% 3.42/0.99  ------ AIG Options
% 3.42/0.99  
% 3.42/0.99  --aig_mode                              false
% 3.42/0.99  
% 3.42/0.99  ------ Instantiation Options
% 3.42/0.99  
% 3.42/0.99  --instantiation_flag                    true
% 3.42/0.99  --inst_sos_flag                         false
% 3.42/0.99  --inst_sos_phase                        true
% 3.42/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel_side                     num_symb
% 3.42/0.99  --inst_solver_per_active                1400
% 3.42/0.99  --inst_solver_calls_frac                1.
% 3.42/0.99  --inst_passive_queue_type               priority_queues
% 3.42/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.99  --inst_passive_queues_freq              [25;2]
% 3.42/0.99  --inst_dismatching                      true
% 3.42/0.99  --inst_eager_unprocessed_to_passive     true
% 3.42/0.99  --inst_prop_sim_given                   true
% 3.42/0.99  --inst_prop_sim_new                     false
% 3.42/0.99  --inst_subs_new                         false
% 3.42/0.99  --inst_eq_res_simp                      false
% 3.42/0.99  --inst_subs_given                       false
% 3.42/0.99  --inst_orphan_elimination               true
% 3.42/0.99  --inst_learning_loop_flag               true
% 3.42/0.99  --inst_learning_start                   3000
% 3.42/0.99  --inst_learning_factor                  2
% 3.42/0.99  --inst_start_prop_sim_after_learn       3
% 3.42/0.99  --inst_sel_renew                        solver
% 3.42/0.99  --inst_lit_activity_flag                true
% 3.42/0.99  --inst_restr_to_given                   false
% 3.42/0.99  --inst_activity_threshold               500
% 3.42/0.99  --inst_out_proof                        true
% 3.42/0.99  
% 3.42/0.99  ------ Resolution Options
% 3.42/0.99  
% 3.42/0.99  --resolution_flag                       true
% 3.42/0.99  --res_lit_sel                           adaptive
% 3.42/0.99  --res_lit_sel_side                      none
% 3.42/0.99  --res_ordering                          kbo
% 3.42/0.99  --res_to_prop_solver                    active
% 3.42/0.99  --res_prop_simpl_new                    false
% 3.42/0.99  --res_prop_simpl_given                  true
% 3.42/0.99  --res_passive_queue_type                priority_queues
% 3.42/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.99  --res_passive_queues_freq               [15;5]
% 3.42/0.99  --res_forward_subs                      full
% 3.42/0.99  --res_backward_subs                     full
% 3.42/0.99  --res_forward_subs_resolution           true
% 3.42/0.99  --res_backward_subs_resolution          true
% 3.42/0.99  --res_orphan_elimination                true
% 3.42/0.99  --res_time_limit                        2.
% 3.42/0.99  --res_out_proof                         true
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Options
% 3.42/0.99  
% 3.42/0.99  --superposition_flag                    true
% 3.42/0.99  --sup_passive_queue_type                priority_queues
% 3.42/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.99  --demod_completeness_check              fast
% 3.42/0.99  --demod_use_ground                      true
% 3.42/0.99  --sup_to_prop_solver                    passive
% 3.42/0.99  --sup_prop_simpl_new                    true
% 3.42/0.99  --sup_prop_simpl_given                  true
% 3.42/0.99  --sup_fun_splitting                     false
% 3.42/0.99  --sup_smt_interval                      50000
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Simplification Setup
% 3.42/0.99  
% 3.42/0.99  --sup_indices_passive                   []
% 3.42/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_full_bw                           [BwDemod]
% 3.42/0.99  --sup_immed_triv                        [TrivRules]
% 3.42/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_immed_bw_main                     []
% 3.42/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  
% 3.42/0.99  ------ Combination Options
% 3.42/0.99  
% 3.42/0.99  --comb_res_mult                         3
% 3.42/0.99  --comb_sup_mult                         2
% 3.42/0.99  --comb_inst_mult                        10
% 3.42/0.99  
% 3.42/0.99  ------ Debug Options
% 3.42/0.99  
% 3.42/0.99  --dbg_backtrace                         false
% 3.42/0.99  --dbg_dump_prop_clauses                 false
% 3.42/0.99  --dbg_dump_prop_clauses_file            -
% 3.42/0.99  --dbg_out_stat                          false
% 3.42/0.99  ------ Parsing...
% 3.42/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.42/0.99  ------ Proving...
% 3.42/0.99  ------ Problem Properties 
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  clauses                                 28
% 3.42/0.99  conjectures                             2
% 3.42/0.99  EPR                                     11
% 3.42/0.99  Horn                                    23
% 3.42/0.99  unary                                   8
% 3.42/0.99  binary                                  8
% 3.42/0.99  lits                                    74
% 3.42/0.99  lits eq                                 6
% 3.42/0.99  fd_pure                                 0
% 3.42/0.99  fd_pseudo                               0
% 3.42/0.99  fd_cond                                 0
% 3.42/0.99  fd_pseudo_cond                          0
% 3.42/0.99  AC symbols                              0
% 3.42/0.99  
% 3.42/0.99  ------ Schedule dynamic 5 is on 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  ------ 
% 3.42/0.99  Current options:
% 3.42/0.99  ------ 
% 3.42/0.99  
% 3.42/0.99  ------ Input Options
% 3.42/0.99  
% 3.42/0.99  --out_options                           all
% 3.42/0.99  --tptp_safe_out                         true
% 3.42/0.99  --problem_path                          ""
% 3.42/0.99  --include_path                          ""
% 3.42/0.99  --clausifier                            res/vclausify_rel
% 3.42/0.99  --clausifier_options                    --mode clausify
% 3.42/0.99  --stdin                                 false
% 3.42/0.99  --stats_out                             all
% 3.42/0.99  
% 3.42/0.99  ------ General Options
% 3.42/0.99  
% 3.42/0.99  --fof                                   false
% 3.42/0.99  --time_out_real                         305.
% 3.42/0.99  --time_out_virtual                      -1.
% 3.42/0.99  --symbol_type_check                     false
% 3.42/0.99  --clausify_out                          false
% 3.42/0.99  --sig_cnt_out                           false
% 3.42/0.99  --trig_cnt_out                          false
% 3.42/0.99  --trig_cnt_out_tolerance                1.
% 3.42/0.99  --trig_cnt_out_sk_spl                   false
% 3.42/0.99  --abstr_cl_out                          false
% 3.42/0.99  
% 3.42/0.99  ------ Global Options
% 3.42/0.99  
% 3.42/0.99  --schedule                              default
% 3.42/0.99  --add_important_lit                     false
% 3.42/0.99  --prop_solver_per_cl                    1000
% 3.42/0.99  --min_unsat_core                        false
% 3.42/0.99  --soft_assumptions                      false
% 3.42/0.99  --soft_lemma_size                       3
% 3.42/0.99  --prop_impl_unit_size                   0
% 3.42/0.99  --prop_impl_unit                        []
% 3.42/0.99  --share_sel_clauses                     true
% 3.42/0.99  --reset_solvers                         false
% 3.42/0.99  --bc_imp_inh                            [conj_cone]
% 3.42/0.99  --conj_cone_tolerance                   3.
% 3.42/0.99  --extra_neg_conj                        none
% 3.42/0.99  --large_theory_mode                     true
% 3.42/0.99  --prolific_symb_bound                   200
% 3.42/0.99  --lt_threshold                          2000
% 3.42/0.99  --clause_weak_htbl                      true
% 3.42/0.99  --gc_record_bc_elim                     false
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing Options
% 3.42/0.99  
% 3.42/0.99  --preprocessing_flag                    true
% 3.42/0.99  --time_out_prep_mult                    0.1
% 3.42/0.99  --splitting_mode                        input
% 3.42/0.99  --splitting_grd                         true
% 3.42/0.99  --splitting_cvd                         false
% 3.42/0.99  --splitting_cvd_svl                     false
% 3.42/0.99  --splitting_nvd                         32
% 3.42/0.99  --sub_typing                            true
% 3.42/0.99  --prep_gs_sim                           true
% 3.42/0.99  --prep_unflatten                        true
% 3.42/0.99  --prep_res_sim                          true
% 3.42/0.99  --prep_upred                            true
% 3.42/0.99  --prep_sem_filter                       exhaustive
% 3.42/0.99  --prep_sem_filter_out                   false
% 3.42/0.99  --pred_elim                             true
% 3.42/0.99  --res_sim_input                         true
% 3.42/0.99  --eq_ax_congr_red                       true
% 3.42/0.99  --pure_diseq_elim                       true
% 3.42/0.99  --brand_transform                       false
% 3.42/0.99  --non_eq_to_eq                          false
% 3.42/0.99  --prep_def_merge                        true
% 3.42/0.99  --prep_def_merge_prop_impl              false
% 3.42/0.99  --prep_def_merge_mbd                    true
% 3.42/0.99  --prep_def_merge_tr_red                 false
% 3.42/0.99  --prep_def_merge_tr_cl                  false
% 3.42/0.99  --smt_preprocessing                     true
% 3.42/0.99  --smt_ac_axioms                         fast
% 3.42/0.99  --preprocessed_out                      false
% 3.42/0.99  --preprocessed_stats                    false
% 3.42/0.99  
% 3.42/0.99  ------ Abstraction refinement Options
% 3.42/0.99  
% 3.42/0.99  --abstr_ref                             []
% 3.42/0.99  --abstr_ref_prep                        false
% 3.42/0.99  --abstr_ref_until_sat                   false
% 3.42/0.99  --abstr_ref_sig_restrict                funpre
% 3.42/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.99  --abstr_ref_under                       []
% 3.42/0.99  
% 3.42/0.99  ------ SAT Options
% 3.42/0.99  
% 3.42/0.99  --sat_mode                              false
% 3.42/0.99  --sat_fm_restart_options                ""
% 3.42/0.99  --sat_gr_def                            false
% 3.42/0.99  --sat_epr_types                         true
% 3.42/0.99  --sat_non_cyclic_types                  false
% 3.42/0.99  --sat_finite_models                     false
% 3.42/0.99  --sat_fm_lemmas                         false
% 3.42/0.99  --sat_fm_prep                           false
% 3.42/0.99  --sat_fm_uc_incr                        true
% 3.42/0.99  --sat_out_model                         small
% 3.42/0.99  --sat_out_clauses                       false
% 3.42/0.99  
% 3.42/0.99  ------ QBF Options
% 3.42/0.99  
% 3.42/0.99  --qbf_mode                              false
% 3.42/0.99  --qbf_elim_univ                         false
% 3.42/0.99  --qbf_dom_inst                          none
% 3.42/0.99  --qbf_dom_pre_inst                      false
% 3.42/0.99  --qbf_sk_in                             false
% 3.42/0.99  --qbf_pred_elim                         true
% 3.42/0.99  --qbf_split                             512
% 3.42/0.99  
% 3.42/0.99  ------ BMC1 Options
% 3.42/0.99  
% 3.42/0.99  --bmc1_incremental                      false
% 3.42/0.99  --bmc1_axioms                           reachable_all
% 3.42/0.99  --bmc1_min_bound                        0
% 3.42/0.99  --bmc1_max_bound                        -1
% 3.42/0.99  --bmc1_max_bound_default                -1
% 3.42/0.99  --bmc1_symbol_reachability              true
% 3.42/0.99  --bmc1_property_lemmas                  false
% 3.42/0.99  --bmc1_k_induction                      false
% 3.42/0.99  --bmc1_non_equiv_states                 false
% 3.42/0.99  --bmc1_deadlock                         false
% 3.42/0.99  --bmc1_ucm                              false
% 3.42/0.99  --bmc1_add_unsat_core                   none
% 3.42/0.99  --bmc1_unsat_core_children              false
% 3.42/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.99  --bmc1_out_stat                         full
% 3.42/0.99  --bmc1_ground_init                      false
% 3.42/0.99  --bmc1_pre_inst_next_state              false
% 3.42/0.99  --bmc1_pre_inst_state                   false
% 3.42/0.99  --bmc1_pre_inst_reach_state             false
% 3.42/0.99  --bmc1_out_unsat_core                   false
% 3.42/0.99  --bmc1_aig_witness_out                  false
% 3.42/0.99  --bmc1_verbose                          false
% 3.42/0.99  --bmc1_dump_clauses_tptp                false
% 3.42/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.99  --bmc1_dump_file                        -
% 3.42/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.99  --bmc1_ucm_extend_mode                  1
% 3.42/0.99  --bmc1_ucm_init_mode                    2
% 3.42/0.99  --bmc1_ucm_cone_mode                    none
% 3.42/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.99  --bmc1_ucm_relax_model                  4
% 3.42/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.99  --bmc1_ucm_layered_model                none
% 3.42/0.99  --bmc1_ucm_max_lemma_size               10
% 3.42/0.99  
% 3.42/0.99  ------ AIG Options
% 3.42/0.99  
% 3.42/0.99  --aig_mode                              false
% 3.42/0.99  
% 3.42/0.99  ------ Instantiation Options
% 3.42/0.99  
% 3.42/0.99  --instantiation_flag                    true
% 3.42/0.99  --inst_sos_flag                         false
% 3.42/0.99  --inst_sos_phase                        true
% 3.42/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.99  --inst_lit_sel_side                     none
% 3.42/0.99  --inst_solver_per_active                1400
% 3.42/0.99  --inst_solver_calls_frac                1.
% 3.42/0.99  --inst_passive_queue_type               priority_queues
% 3.42/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.99  --inst_passive_queues_freq              [25;2]
% 3.42/0.99  --inst_dismatching                      true
% 3.42/0.99  --inst_eager_unprocessed_to_passive     true
% 3.42/0.99  --inst_prop_sim_given                   true
% 3.42/0.99  --inst_prop_sim_new                     false
% 3.42/0.99  --inst_subs_new                         false
% 3.42/0.99  --inst_eq_res_simp                      false
% 3.42/0.99  --inst_subs_given                       false
% 3.42/0.99  --inst_orphan_elimination               true
% 3.42/0.99  --inst_learning_loop_flag               true
% 3.42/0.99  --inst_learning_start                   3000
% 3.42/0.99  --inst_learning_factor                  2
% 3.42/0.99  --inst_start_prop_sim_after_learn       3
% 3.42/0.99  --inst_sel_renew                        solver
% 3.42/0.99  --inst_lit_activity_flag                true
% 3.42/0.99  --inst_restr_to_given                   false
% 3.42/0.99  --inst_activity_threshold               500
% 3.42/0.99  --inst_out_proof                        true
% 3.42/0.99  
% 3.42/0.99  ------ Resolution Options
% 3.42/0.99  
% 3.42/0.99  --resolution_flag                       false
% 3.42/0.99  --res_lit_sel                           adaptive
% 3.42/0.99  --res_lit_sel_side                      none
% 3.42/0.99  --res_ordering                          kbo
% 3.42/0.99  --res_to_prop_solver                    active
% 3.42/0.99  --res_prop_simpl_new                    false
% 3.42/0.99  --res_prop_simpl_given                  true
% 3.42/0.99  --res_passive_queue_type                priority_queues
% 3.42/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.99  --res_passive_queues_freq               [15;5]
% 3.42/0.99  --res_forward_subs                      full
% 3.42/0.99  --res_backward_subs                     full
% 3.42/0.99  --res_forward_subs_resolution           true
% 3.42/0.99  --res_backward_subs_resolution          true
% 3.42/0.99  --res_orphan_elimination                true
% 3.42/0.99  --res_time_limit                        2.
% 3.42/0.99  --res_out_proof                         true
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Options
% 3.42/0.99  
% 3.42/0.99  --superposition_flag                    true
% 3.42/0.99  --sup_passive_queue_type                priority_queues
% 3.42/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.99  --demod_completeness_check              fast
% 3.42/0.99  --demod_use_ground                      true
% 3.42/0.99  --sup_to_prop_solver                    passive
% 3.42/0.99  --sup_prop_simpl_new                    true
% 3.42/0.99  --sup_prop_simpl_given                  true
% 3.42/0.99  --sup_fun_splitting                     false
% 3.42/0.99  --sup_smt_interval                      50000
% 3.42/0.99  
% 3.42/0.99  ------ Superposition Simplification Setup
% 3.42/0.99  
% 3.42/0.99  --sup_indices_passive                   []
% 3.42/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_full_bw                           [BwDemod]
% 3.42/0.99  --sup_immed_triv                        [TrivRules]
% 3.42/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_immed_bw_main                     []
% 3.42/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.99  
% 3.42/0.99  ------ Combination Options
% 3.42/0.99  
% 3.42/0.99  --comb_res_mult                         3
% 3.42/0.99  --comb_sup_mult                         2
% 3.42/0.99  --comb_inst_mult                        10
% 3.42/0.99  
% 3.42/0.99  ------ Debug Options
% 3.42/0.99  
% 3.42/0.99  --dbg_backtrace                         false
% 3.42/0.99  --dbg_dump_prop_clauses                 false
% 3.42/0.99  --dbg_dump_prop_clauses_file            -
% 3.42/0.99  --dbg_out_stat                          false
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  ------ Proving...
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  % SZS status Theorem for theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  fof(f5,axiom,(
% 3.42/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f16,plain,(
% 3.42/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.42/0.99    inference(ennf_transformation,[],[f5])).
% 3.42/0.99  
% 3.42/0.99  fof(f59,plain,(
% 3.42/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f16])).
% 3.42/0.99  
% 3.42/0.99  fof(f6,axiom,(
% 3.42/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f17,plain,(
% 3.42/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.42/0.99    inference(ennf_transformation,[],[f6])).
% 3.42/0.99  
% 3.42/0.99  fof(f60,plain,(
% 3.42/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f17])).
% 3.42/0.99  
% 3.42/0.99  fof(f9,conjecture,(
% 3.42/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f10,negated_conjecture,(
% 3.42/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.42/0.99    inference(negated_conjecture,[],[f9])).
% 3.42/0.99  
% 3.42/0.99  fof(f11,plain,(
% 3.42/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.42/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.42/0.99  
% 3.42/0.99  fof(f12,plain,(
% 3.42/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.42/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.42/0.99  
% 3.42/0.99  fof(f21,plain,(
% 3.42/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.42/0.99    inference(ennf_transformation,[],[f12])).
% 3.42/0.99  
% 3.42/0.99  fof(f22,plain,(
% 3.42/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.42/0.99    inference(flattening,[],[f21])).
% 3.42/0.99  
% 3.42/0.99  fof(f39,plain,(
% 3.42/0.99    ( ! [X2,X0,X1] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) => ((r1_tsep_1(sK8,X2) | r1_tsep_1(X2,sK8)) & (~r1_tsep_1(sK8,X1) | ~r1_tsep_1(X1,sK8)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK8,X0))) )),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f38,plain,(
% 3.42/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) => (? [X3] : ((r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,sK7) & m1_pre_topc(X3,X0)) & m1_pre_topc(sK7,X0))) )),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f37,plain,(
% 3.42/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK6,X0))) )),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f36,plain,(
% 3.42/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5)) & m1_pre_topc(X2,sK5)) & m1_pre_topc(X1,sK5)) & l1_pre_topc(sK5))),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f40,plain,(
% 3.42/0.99    ((((r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & (~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5)) & m1_pre_topc(sK7,sK5)) & m1_pre_topc(sK6,sK5)) & l1_pre_topc(sK5)),
% 3.42/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f22,f39,f38,f37,f36])).
% 3.42/0.99  
% 3.42/0.99  fof(f67,plain,(
% 3.42/0.99    m1_pre_topc(sK8,sK5)),
% 3.42/0.99    inference(cnf_transformation,[],[f40])).
% 3.42/0.99  
% 3.42/0.99  fof(f64,plain,(
% 3.42/0.99    l1_pre_topc(sK5)),
% 3.42/0.99    inference(cnf_transformation,[],[f40])).
% 3.42/0.99  
% 3.42/0.99  fof(f3,axiom,(
% 3.42/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f14,plain,(
% 3.42/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.42/0.99    inference(ennf_transformation,[],[f3])).
% 3.42/0.99  
% 3.42/0.99  fof(f45,plain,(
% 3.42/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f14])).
% 3.42/0.99  
% 3.42/0.99  fof(f66,plain,(
% 3.42/0.99    m1_pre_topc(sK7,sK5)),
% 3.42/0.99    inference(cnf_transformation,[],[f40])).
% 3.42/0.99  
% 3.42/0.99  fof(f68,plain,(
% 3.42/0.99    m1_pre_topc(sK6,sK7)),
% 3.42/0.99    inference(cnf_transformation,[],[f40])).
% 3.42/0.99  
% 3.42/0.99  fof(f7,axiom,(
% 3.42/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f18,plain,(
% 3.42/0.99    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.42/0.99    inference(ennf_transformation,[],[f7])).
% 3.42/0.99  
% 3.42/0.99  fof(f35,plain,(
% 3.42/0.99    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.42/0.99    inference(nnf_transformation,[],[f18])).
% 3.42/0.99  
% 3.42/0.99  fof(f62,plain,(
% 3.42/0.99    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f35])).
% 3.42/0.99  
% 3.42/0.99  fof(f23,plain,(
% 3.42/0.99    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 3.42/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.42/0.99  
% 3.42/0.99  fof(f28,plain,(
% 3.42/0.99    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.42/0.99    inference(nnf_transformation,[],[f23])).
% 3.42/0.99  
% 3.42/0.99  fof(f29,plain,(
% 3.42/0.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.42/0.99    inference(flattening,[],[f28])).
% 3.42/0.99  
% 3.42/0.99  fof(f30,plain,(
% 3.42/0.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.42/0.99    inference(rectify,[],[f29])).
% 3.42/0.99  
% 3.42/0.99  fof(f33,plain,(
% 3.42/0.99    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f32,plain,(
% 3.42/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f31,plain,(
% 3.42/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.42/0.99    introduced(choice_axiom,[])).
% 3.42/0.99  
% 3.42/0.99  fof(f34,plain,(
% 3.42/0.99    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.42/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).
% 3.42/0.99  
% 3.42/0.99  fof(f48,plain,(
% 3.42/0.99    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f34])).
% 3.42/0.99  
% 3.42/0.99  fof(f4,axiom,(
% 3.42/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f15,plain,(
% 3.42/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.42/0.99    inference(ennf_transformation,[],[f4])).
% 3.42/0.99  
% 3.42/0.99  fof(f24,plain,(
% 3.42/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 3.42/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.42/0.99  
% 3.42/0.99  fof(f25,plain,(
% 3.42/0.99    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.42/0.99    inference(definition_folding,[],[f15,f24,f23])).
% 3.42/0.99  
% 3.42/0.99  fof(f58,plain,(
% 3.42/0.99    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f25])).
% 3.42/0.99  
% 3.42/0.99  fof(f27,plain,(
% 3.42/0.99    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 3.42/0.99    inference(nnf_transformation,[],[f24])).
% 3.42/0.99  
% 3.42/0.99  fof(f46,plain,(
% 3.42/0.99    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f27])).
% 3.42/0.99  
% 3.42/0.99  fof(f61,plain,(
% 3.42/0.99    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f35])).
% 3.42/0.99  
% 3.42/0.99  fof(f2,axiom,(
% 3.42/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f26,plain,(
% 3.42/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.42/0.99    inference(nnf_transformation,[],[f2])).
% 3.42/0.99  
% 3.42/0.99  fof(f43,plain,(
% 3.42/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f26])).
% 3.42/0.99  
% 3.42/0.99  fof(f8,axiom,(
% 3.42/0.99    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f19,plain,(
% 3.42/0.99    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.42/0.99    inference(ennf_transformation,[],[f8])).
% 3.42/0.99  
% 3.42/0.99  fof(f20,plain,(
% 3.42/0.99    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.42/0.99    inference(flattening,[],[f19])).
% 3.42/0.99  
% 3.42/0.99  fof(f63,plain,(
% 3.42/0.99    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.42/0.99    inference(cnf_transformation,[],[f20])).
% 3.42/0.99  
% 3.42/0.99  fof(f70,plain,(
% 3.42/0.99    r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)),
% 3.42/0.99    inference(cnf_transformation,[],[f40])).
% 3.42/0.99  
% 3.42/0.99  fof(f1,axiom,(
% 3.42/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.42/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.99  
% 3.42/0.99  fof(f13,plain,(
% 3.42/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.42/0.99    inference(ennf_transformation,[],[f1])).
% 3.42/0.99  
% 3.42/0.99  fof(f42,plain,(
% 3.42/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.42/0.99    inference(cnf_transformation,[],[f13])).
% 3.42/0.99  
% 3.42/0.99  fof(f69,plain,(
% 3.42/0.99    ~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)),
% 3.42/0.99    inference(cnf_transformation,[],[f40])).
% 3.42/0.99  
% 3.42/0.99  cnf(c_18,plain,
% 3.42/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_19,plain,
% 3.42/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_26,negated_conjecture,
% 3.42/0.99      ( m1_pre_topc(sK8,sK5) ),
% 3.42/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_555,plain,
% 3.42/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X0 | sK8 != X1 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_556,plain,
% 3.42/0.99      ( ~ l1_pre_topc(sK5) | l1_pre_topc(sK8) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_555]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_29,negated_conjecture,
% 3.42/0.99      ( l1_pre_topc(sK5) ),
% 3.42/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_558,plain,
% 3.42/0.99      ( l1_pre_topc(sK8) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_556,c_29]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_626,plain,
% 3.42/0.99      ( l1_struct_0(X0) | sK8 != X0 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_558]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_627,plain,
% 3.42/0.99      ( l1_struct_0(sK8) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_626]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3531,plain,
% 3.42/0.99      ( l1_struct_0(sK8) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4,plain,
% 3.42/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3552,plain,
% 3.42/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.42/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3946,plain,
% 3.42/0.99      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3531,c_3552]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_27,negated_conjecture,
% 3.42/0.99      ( m1_pre_topc(sK7,sK5) ),
% 3.42/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_577,plain,
% 3.42/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X0 | sK7 != X1 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_578,plain,
% 3.42/0.99      ( ~ l1_pre_topc(sK5) | l1_pre_topc(sK7) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_577]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_580,plain,
% 3.42/0.99      ( l1_pre_topc(sK7) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_578,c_29]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_25,negated_conjecture,
% 3.42/0.99      ( m1_pre_topc(sK6,sK7) ),
% 3.42/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_534,plain,
% 3.42/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X1 | sK7 != X0 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_535,plain,
% 3.42/0.99      ( l1_pre_topc(sK6) | ~ l1_pre_topc(sK7) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_534]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_588,plain,
% 3.42/0.99      ( l1_pre_topc(sK6) ),
% 3.42/0.99      inference(backward_subsumption_resolution,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_580,c_535]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_640,plain,
% 3.42/0.99      ( l1_struct_0(X0) | sK6 != X0 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_588]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_641,plain,
% 3.42/0.99      ( l1_struct_0(sK6) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_640]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3529,plain,
% 3.42/0.99      ( l1_struct_0(sK6) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3949,plain,
% 3.42/0.99      ( u1_struct_0(sK6) = k2_struct_0(sK6) ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3529,c_3552]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_20,plain,
% 3.42/0.99      ( r1_tsep_1(X0,X1)
% 3.42/0.99      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.42/0.99      | ~ l1_struct_0(X0)
% 3.42/0.99      | ~ l1_struct_0(X1) ),
% 3.42/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3541,plain,
% 3.42/0.99      ( r1_tsep_1(X0,X1) = iProver_top
% 3.42/0.99      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.42/0.99      | l1_struct_0(X0) != iProver_top
% 3.42/0.99      | l1_struct_0(X1) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4506,plain,
% 3.42/0.99      ( r1_tsep_1(sK6,X0) = iProver_top
% 3.42/0.99      | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) != iProver_top
% 3.42/0.99      | l1_struct_0(X0) != iProver_top
% 3.42/0.99      | l1_struct_0(sK6) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3949,c_3541]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_642,plain,
% 3.42/0.99      ( l1_struct_0(sK6) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_12005,plain,
% 3.42/0.99      ( l1_struct_0(X0) != iProver_top
% 3.42/0.99      | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) != iProver_top
% 3.42/0.99      | r1_tsep_1(sK6,X0) = iProver_top ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_4506,c_642]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_12006,plain,
% 3.42/0.99      ( r1_tsep_1(sK6,X0) = iProver_top
% 3.42/0.99      | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) != iProver_top
% 3.42/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.42/0.99      inference(renaming,[status(thm)],[c_12005]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_12015,plain,
% 3.42/0.99      ( r1_tsep_1(sK6,sK8) = iProver_top
% 3.42/0.99      | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) != iProver_top
% 3.42/0.99      | l1_struct_0(sK8) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3946,c_12006]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_30,plain,
% 3.42/0.99      ( l1_pre_topc(sK5) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_45,plain,
% 3.42/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_47,plain,
% 3.42/0.99      ( l1_pre_topc(sK8) != iProver_top
% 3.42/0.99      | l1_struct_0(sK8) = iProver_top ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_45]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_557,plain,
% 3.42/0.99      ( l1_pre_topc(sK5) != iProver_top
% 3.42/0.99      | l1_pre_topc(sK8) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_633,plain,
% 3.42/0.99      ( l1_struct_0(X0) | sK7 != X0 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_580]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_634,plain,
% 3.42/0.99      ( l1_struct_0(sK7) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_633]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_635,plain,
% 3.42/0.99      ( l1_struct_0(sK7) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_16,plain,
% 3.42/0.99      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.42/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_17,plain,
% 3.42/0.99      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6,plain,
% 3.42/0.99      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 3.42/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_396,plain,
% 3.42/0.99      ( sP0(X0,X1)
% 3.42/0.99      | ~ m1_pre_topc(X0,X1)
% 3.42/0.99      | ~ l1_pre_topc(X0)
% 3.42/0.99      | ~ l1_pre_topc(X1) ),
% 3.42/0.99      inference(resolution,[status(thm)],[c_17,c_6]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_400,plain,
% 3.42/0.99      ( ~ m1_pre_topc(X0,X1) | sP0(X0,X1) | ~ l1_pre_topc(X1) ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_396,c_19]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_401,plain,
% 3.42/0.99      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 3.42/0.99      inference(renaming,[status(thm)],[c_400]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_524,plain,
% 3.42/0.99      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK6 != X0 | sK7 != X1 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_401,c_25]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_525,plain,
% 3.42/0.99      ( sP0(sK6,sK7) | ~ l1_pre_topc(sK7) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_524]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_587,plain,
% 3.42/0.99      ( sP0(sK6,sK7) ),
% 3.42/0.99      inference(backward_subsumption_resolution,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_580,c_525]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1239,plain,
% 3.42/0.99      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
% 3.42/0.99      | sK6 != X0
% 3.42/0.99      | sK7 != X1 ),
% 3.42/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_587]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1240,plain,
% 3.42/0.99      ( r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7)) ),
% 3.42/0.99      inference(unflattening,[status(thm)],[c_1239]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_1241,plain,
% 3.42/0.99      ( r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7)) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_21,plain,
% 3.42/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.42/0.99      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.42/0.99      | ~ l1_struct_0(X0)
% 3.42/0.99      | ~ l1_struct_0(X1) ),
% 3.42/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3774,plain,
% 3.42/0.99      ( ~ r1_tsep_1(sK7,sK8)
% 3.42/0.99      | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 3.42/0.99      | ~ l1_struct_0(sK7)
% 3.42/0.99      | ~ l1_struct_0(sK8) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3775,plain,
% 3.42/0.99      ( r1_tsep_1(sK7,sK8) != iProver_top
% 3.42/0.99      | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = iProver_top
% 3.42/0.99      | l1_struct_0(sK7) != iProver_top
% 3.42/0.99      | l1_struct_0(sK8) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_3774]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3,plain,
% 3.42/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.42/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3887,plain,
% 3.42/0.99      ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))
% 3.42/0.99      | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = u1_struct_0(sK7) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3888,plain,
% 3.42/0.99      ( k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = u1_struct_0(sK7)
% 3.42/0.99      | r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_3887]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_22,plain,
% 3.42/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.42/0.99      | r1_tsep_1(X1,X0)
% 3.42/0.99      | ~ l1_struct_0(X0)
% 3.42/0.99      | ~ l1_struct_0(X1) ),
% 3.42/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3898,plain,
% 3.42/0.99      ( r1_tsep_1(sK7,sK8)
% 3.42/0.99      | ~ r1_tsep_1(sK8,sK7)
% 3.42/0.99      | ~ l1_struct_0(sK7)
% 3.42/0.99      | ~ l1_struct_0(sK8) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3902,plain,
% 3.42/0.99      ( r1_tsep_1(sK7,sK8) = iProver_top
% 3.42/0.99      | r1_tsep_1(sK8,sK7) != iProver_top
% 3.42/0.99      | l1_struct_0(sK7) != iProver_top
% 3.42/0.99      | l1_struct_0(sK8) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_3898]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3530,plain,
% 3.42/0.99      ( l1_struct_0(sK7) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3948,plain,
% 3.42/0.99      ( u1_struct_0(sK7) = k2_struct_0(sK7) ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3530,c_3552]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_2855,plain,( X0 = X0 ),theory(equality) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4293,plain,
% 3.42/0.99      ( k2_struct_0(sK6) = k2_struct_0(sK6) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_2855]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_23,negated_conjecture,
% 3.42/0.99      ( r1_tsep_1(sK7,sK8) | r1_tsep_1(sK8,sK7) ),
% 3.42/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3538,plain,
% 3.42/0.99      ( r1_tsep_1(sK7,sK8) = iProver_top
% 3.42/0.99      | r1_tsep_1(sK8,sK7) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3539,plain,
% 3.42/0.99      ( r1_tsep_1(X0,X1) != iProver_top
% 3.42/0.99      | r1_tsep_1(X1,X0) = iProver_top
% 3.42/0.99      | l1_struct_0(X0) != iProver_top
% 3.42/0.99      | l1_struct_0(X1) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4317,plain,
% 3.42/0.99      ( r1_tsep_1(sK8,sK7) = iProver_top
% 3.42/0.99      | l1_struct_0(sK7) != iProver_top
% 3.42/0.99      | l1_struct_0(sK8) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_3538,c_3539]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4581,plain,
% 3.42/0.99      ( r1_tsep_1(sK6,sK8) = iProver_top
% 3.42/0.99      | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) != iProver_top
% 3.42/0.99      | l1_struct_0(sK6) != iProver_top
% 3.42/0.99      | l1_struct_0(sK8) != iProver_top ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_4506]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_2856,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4029,plain,
% 3.42/0.99      ( X0 != X1 | X0 = u1_struct_0(sK7) | u1_struct_0(sK7) != X1 ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_2856]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4202,plain,
% 3.42/0.99      ( X0 = u1_struct_0(sK7)
% 3.42/0.99      | X0 != k2_struct_0(sK7)
% 3.42/0.99      | u1_struct_0(sK7) != k2_struct_0(sK7) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_4029]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4858,plain,
% 3.42/0.99      ( u1_struct_0(sK7) != k2_struct_0(sK7)
% 3.42/0.99      | k2_struct_0(sK7) = u1_struct_0(sK7)
% 3.42/0.99      | k2_struct_0(sK7) != k2_struct_0(sK7) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_4202]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4859,plain,
% 3.42/0.99      ( k2_struct_0(sK7) = k2_struct_0(sK7) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_2855]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_3979,plain,
% 3.42/0.99      ( X0 != X1 | k4_xboole_0(X2,X3) != X1 | k4_xboole_0(X2,X3) = X0 ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_2856]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4307,plain,
% 3.42/0.99      ( X0 != u1_struct_0(sK7)
% 3.42/0.99      | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = X0
% 3.42/0.99      | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != u1_struct_0(sK7) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_3979]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_5576,plain,
% 3.42/0.99      ( k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != u1_struct_0(sK7)
% 3.42/0.99      | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) = k2_struct_0(sK7)
% 3.42/0.99      | k2_struct_0(sK7) != u1_struct_0(sK7) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_4307]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_2858,plain,
% 3.42/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.42/0.99      theory(equality) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4054,plain,
% 3.42/0.99      ( r1_tarski(X0,X1)
% 3.42/0.99      | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
% 3.42/0.99      | X0 != k2_struct_0(sK6)
% 3.42/0.99      | X1 != k2_struct_0(sK7) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_2858]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_4292,plain,
% 3.42/0.99      ( r1_tarski(k2_struct_0(sK6),X0)
% 3.42/0.99      | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
% 3.42/0.99      | X0 != k2_struct_0(sK7)
% 3.42/0.99      | k2_struct_0(sK6) != k2_struct_0(sK6) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_4054]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6214,plain,
% 3.42/0.99      ( r1_tarski(k2_struct_0(sK6),k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)))
% 3.42/0.99      | ~ r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7))
% 3.42/0.99      | k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != k2_struct_0(sK7)
% 3.42/0.99      | k2_struct_0(sK6) != k2_struct_0(sK6) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_4292]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_6225,plain,
% 3.42/0.99      ( k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)) != k2_struct_0(sK7)
% 3.42/0.99      | k2_struct_0(sK6) != k2_struct_0(sK6)
% 3.42/0.99      | r1_tarski(k2_struct_0(sK6),k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))) = iProver_top
% 3.42/0.99      | r1_tarski(k2_struct_0(sK6),k2_struct_0(sK7)) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_6214]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_0,plain,
% 3.42/0.99      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 3.42/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7020,plain,
% 3.42/0.99      ( ~ r1_tarski(k2_struct_0(sK6),k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8)))
% 3.42/0.99      | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) ),
% 3.42/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_7021,plain,
% 3.42/0.99      ( r1_tarski(k2_struct_0(sK6),k4_xboole_0(u1_struct_0(sK7),u1_struct_0(sK8))) != iProver_top
% 3.42/0.99      | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(sK8)) = iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_7020]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_12041,plain,
% 3.42/0.99      ( r1_tsep_1(sK6,sK8) = iProver_top ),
% 3.42/0.99      inference(global_propositional_subsumption,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_12015,c_30,c_47,c_557,c_635,c_642,c_1241,c_3775,
% 3.42/0.99                 c_3888,c_3902,c_3948,c_4293,c_4317,c_4581,c_4858,c_4859,
% 3.42/0.99                 c_5576,c_6225,c_7021]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_12047,plain,
% 3.42/0.99      ( r1_tsep_1(sK8,sK6) = iProver_top
% 3.42/0.99      | l1_struct_0(sK6) != iProver_top
% 3.42/0.99      | l1_struct_0(sK8) != iProver_top ),
% 3.42/0.99      inference(superposition,[status(thm)],[c_12041,c_3539]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_24,negated_conjecture,
% 3.42/0.99      ( ~ r1_tsep_1(sK6,sK8) | ~ r1_tsep_1(sK8,sK6) ),
% 3.42/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(c_35,plain,
% 3.42/0.99      ( r1_tsep_1(sK6,sK8) != iProver_top
% 3.42/0.99      | r1_tsep_1(sK8,sK6) != iProver_top ),
% 3.42/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.42/0.99  
% 3.42/0.99  cnf(contradiction,plain,
% 3.42/0.99      ( $false ),
% 3.42/0.99      inference(minisat,
% 3.42/0.99                [status(thm)],
% 3.42/0.99                [c_12047,c_7021,c_6225,c_5576,c_4859,c_4858,c_4581,
% 3.42/0.99                 c_4317,c_4293,c_3948,c_3902,c_3888,c_3775,c_1241,c_642,
% 3.42/0.99                 c_635,c_557,c_47,c_35,c_30]) ).
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.42/0.99  
% 3.42/0.99  ------                               Statistics
% 3.42/0.99  
% 3.42/0.99  ------ General
% 3.42/0.99  
% 3.42/0.99  abstr_ref_over_cycles:                  0
% 3.42/0.99  abstr_ref_under_cycles:                 0
% 3.42/0.99  gc_basic_clause_elim:                   0
% 3.42/0.99  forced_gc_time:                         0
% 3.42/0.99  parsing_time:                           0.009
% 3.42/0.99  unif_index_cands_time:                  0.
% 3.42/0.99  unif_index_add_time:                    0.
% 3.42/0.99  orderings_time:                         0.
% 3.42/0.99  out_proof_time:                         0.01
% 3.42/0.99  total_time:                             0.303
% 3.42/0.99  num_of_symbols:                         54
% 3.42/0.99  num_of_terms:                           5561
% 3.42/0.99  
% 3.42/0.99  ------ Preprocessing
% 3.42/0.99  
% 3.42/0.99  num_of_splits:                          0
% 3.42/0.99  num_of_split_atoms:                     0
% 3.42/0.99  num_of_reused_defs:                     0
% 3.42/0.99  num_eq_ax_congr_red:                    41
% 3.42/0.99  num_of_sem_filtered_clauses:            1
% 3.42/0.99  num_of_subtypes:                        0
% 3.42/0.99  monotx_restored_types:                  0
% 3.42/0.99  sat_num_of_epr_types:                   0
% 3.42/0.99  sat_num_of_non_cyclic_types:            0
% 3.42/0.99  sat_guarded_non_collapsed_types:        0
% 3.42/0.99  num_pure_diseq_elim:                    0
% 3.42/0.99  simp_replaced_by:                       0
% 3.42/0.99  res_preprocessed:                       137
% 3.42/0.99  prep_upred:                             0
% 3.42/0.99  prep_unflattend:                        196
% 3.42/0.99  smt_new_axioms:                         0
% 3.42/0.99  pred_elim_cands:                        7
% 3.42/0.99  pred_elim:                              3
% 3.42/0.99  pred_elim_cl:                           2
% 3.42/0.99  pred_elim_cycles:                       7
% 3.42/0.99  merged_defs:                            8
% 3.42/0.99  merged_defs_ncl:                        0
% 3.42/0.99  bin_hyper_res:                          8
% 3.42/0.99  prep_cycles:                            4
% 3.42/0.99  pred_elim_time:                         0.044
% 3.42/0.99  splitting_time:                         0.
% 3.42/0.99  sem_filter_time:                        0.
% 3.42/0.99  monotx_time:                            0.001
% 3.42/0.99  subtype_inf_time:                       0.
% 3.42/0.99  
% 3.42/0.99  ------ Problem properties
% 3.42/0.99  
% 3.42/0.99  clauses:                                28
% 3.42/0.99  conjectures:                            2
% 3.42/0.99  epr:                                    11
% 3.42/0.99  horn:                                   23
% 3.42/0.99  ground:                                 10
% 3.42/0.99  unary:                                  8
% 3.42/0.99  binary:                                 8
% 3.42/0.99  lits:                                   74
% 3.42/0.99  lits_eq:                                6
% 3.42/0.99  fd_pure:                                0
% 3.42/0.99  fd_pseudo:                              0
% 3.42/0.99  fd_cond:                                0
% 3.42/0.99  fd_pseudo_cond:                         0
% 3.42/0.99  ac_symbols:                             0
% 3.42/0.99  
% 3.42/0.99  ------ Propositional Solver
% 3.42/0.99  
% 3.42/0.99  prop_solver_calls:                      29
% 3.42/0.99  prop_fast_solver_calls:                 1645
% 3.42/0.99  smt_solver_calls:                       0
% 3.42/0.99  smt_fast_solver_calls:                  0
% 3.42/0.99  prop_num_of_clauses:                    3858
% 3.42/0.99  prop_preprocess_simplified:             9510
% 3.42/0.99  prop_fo_subsumed:                       59
% 3.42/0.99  prop_solver_time:                       0.
% 3.42/0.99  smt_solver_time:                        0.
% 3.42/0.99  smt_fast_solver_time:                   0.
% 3.42/0.99  prop_fast_solver_time:                  0.
% 3.42/0.99  prop_unsat_core_time:                   0.
% 3.42/0.99  
% 3.42/0.99  ------ QBF
% 3.42/0.99  
% 3.42/0.99  qbf_q_res:                              0
% 3.42/0.99  qbf_num_tautologies:                    0
% 3.42/0.99  qbf_prep_cycles:                        0
% 3.42/0.99  
% 3.42/0.99  ------ BMC1
% 3.42/0.99  
% 3.42/0.99  bmc1_current_bound:                     -1
% 3.42/0.99  bmc1_last_solved_bound:                 -1
% 3.42/0.99  bmc1_unsat_core_size:                   -1
% 3.42/0.99  bmc1_unsat_core_parents_size:           -1
% 3.42/0.99  bmc1_merge_next_fun:                    0
% 3.42/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.42/0.99  
% 3.42/0.99  ------ Instantiation
% 3.42/0.99  
% 3.42/0.99  inst_num_of_clauses:                    1517
% 3.42/0.99  inst_num_in_passive:                    171
% 3.42/0.99  inst_num_in_active:                     587
% 3.42/0.99  inst_num_in_unprocessed:                760
% 3.42/0.99  inst_num_of_loops:                      600
% 3.42/0.99  inst_num_of_learning_restarts:          0
% 3.42/0.99  inst_num_moves_active_passive:          6
% 3.42/0.99  inst_lit_activity:                      0
% 3.42/0.99  inst_lit_activity_moves:                0
% 3.42/0.99  inst_num_tautologies:                   0
% 3.42/0.99  inst_num_prop_implied:                  0
% 3.42/0.99  inst_num_existing_simplified:           0
% 3.42/0.99  inst_num_eq_res_simplified:             0
% 3.42/0.99  inst_num_child_elim:                    0
% 3.42/0.99  inst_num_of_dismatching_blockings:      235
% 3.42/0.99  inst_num_of_non_proper_insts:           1647
% 3.42/0.99  inst_num_of_duplicates:                 0
% 3.42/0.99  inst_inst_num_from_inst_to_res:         0
% 3.42/0.99  inst_dismatching_checking_time:         0.
% 3.42/0.99  
% 3.42/0.99  ------ Resolution
% 3.42/0.99  
% 3.42/0.99  res_num_of_clauses:                     0
% 3.42/0.99  res_num_in_passive:                     0
% 3.42/0.99  res_num_in_active:                      0
% 3.42/0.99  res_num_of_loops:                       141
% 3.42/0.99  res_forward_subset_subsumed:            116
% 3.42/0.99  res_backward_subset_subsumed:           6
% 3.42/0.99  res_forward_subsumed:                   0
% 3.42/0.99  res_backward_subsumed:                  0
% 3.42/0.99  res_forward_subsumption_resolution:     0
% 3.42/0.99  res_backward_subsumption_resolution:    2
% 3.42/0.99  res_clause_to_clause_subsumption:       232
% 3.42/0.99  res_orphan_elimination:                 0
% 3.42/0.99  res_tautology_del:                      263
% 3.42/0.99  res_num_eq_res_simplified:              0
% 3.42/0.99  res_num_sel_changes:                    0
% 3.42/0.99  res_moves_from_active_to_pass:          0
% 3.42/0.99  
% 3.42/0.99  ------ Superposition
% 3.42/0.99  
% 3.42/0.99  sup_time_total:                         0.
% 3.42/0.99  sup_time_generating:                    0.
% 3.42/0.99  sup_time_sim_full:                      0.
% 3.42/0.99  sup_time_sim_immed:                     0.
% 3.42/0.99  
% 3.42/0.99  sup_num_of_clauses:                     160
% 3.42/0.99  sup_num_in_active:                      119
% 3.42/0.99  sup_num_in_passive:                     41
% 3.42/0.99  sup_num_of_loops:                       119
% 3.42/0.99  sup_fw_superposition:                   146
% 3.42/0.99  sup_bw_superposition:                   48
% 3.42/0.99  sup_immediate_simplified:               29
% 3.42/0.99  sup_given_eliminated:                   0
% 3.42/0.99  comparisons_done:                       0
% 3.42/0.99  comparisons_avoided:                    0
% 3.42/0.99  
% 3.42/0.99  ------ Simplifications
% 3.42/0.99  
% 3.42/0.99  
% 3.42/0.99  sim_fw_subset_subsumed:                 14
% 3.42/0.99  sim_bw_subset_subsumed:                 7
% 3.42/0.99  sim_fw_subsumed:                        0
% 3.42/0.99  sim_bw_subsumed:                        0
% 3.42/0.99  sim_fw_subsumption_res:                 0
% 3.42/0.99  sim_bw_subsumption_res:                 0
% 3.42/0.99  sim_tautology_del:                      18
% 3.42/0.99  sim_eq_tautology_del:                   7
% 3.42/0.99  sim_eq_res_simp:                        0
% 3.42/0.99  sim_fw_demodulated:                     0
% 3.42/0.99  sim_bw_demodulated:                     0
% 3.42/0.99  sim_light_normalised:                   17
% 3.42/0.99  sim_joinable_taut:                      0
% 3.42/0.99  sim_joinable_simp:                      0
% 3.42/0.99  sim_ac_normalised:                      0
% 3.42/0.99  sim_smt_subsumption:                    0
% 3.42/0.99  
%------------------------------------------------------------------------------
