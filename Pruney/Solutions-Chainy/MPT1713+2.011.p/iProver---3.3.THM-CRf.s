%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:53 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 617 expanded)
%              Number of clauses        :   97 ( 199 expanded)
%              Number of leaves         :   24 ( 164 expanded)
%              Depth                    :   20
%              Number of atoms          :  599 (3777 expanded)
%              Number of equality atoms :  150 ( 248 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,conjecture,(
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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( r1_tsep_1(X2,X1)
            | r1_tsep_1(X1,X2) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( r1_tsep_1(sK9,X1)
          | r1_tsep_1(X1,sK9) )
        & m1_pre_topc(X1,sK9)
        & m1_pre_topc(sK9,X0)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( r1_tsep_1(X2,sK8)
              | r1_tsep_1(sK8,X2) )
            & m1_pre_topc(sK8,X2)
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK8,X0)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK7)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK7)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( r1_tsep_1(sK9,sK8)
      | r1_tsep_1(sK8,sK9) )
    & m1_pre_topc(sK8,sK9)
    & m1_pre_topc(sK9,sK7)
    & ~ v2_struct_0(sK9)
    & m1_pre_topc(sK8,sK7)
    & ~ v2_struct_0(sK8)
    & l1_pre_topc(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f29,f48,f47,f46])).

fof(f79,plain,(
    m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    m1_pre_topc(sK8,sK9) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,
    ( r1_tsep_1(sK9,sK8)
    | r1_tsep_1(sK8,sK9) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
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

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f31,f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f33])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK9,sK7) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_547,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK7 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_548,plain,
    ( ~ l1_pre_topc(sK7)
    | l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_550,plain,
    ( l1_pre_topc(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_30])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK8,sK9) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_526,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK8 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_527,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_558,plain,
    ( l1_pre_topc(sK8) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_550,c_527])).

cnf(c_592,plain,
    ( l1_struct_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_558])).

cnf(c_593,plain,
    ( l1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_1151,plain,
    ( l1_struct_0(sK8) ),
    inference(subtyping,[status(esa)],[c_593])).

cnf(c_1405,plain,
    ( l1_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1157,plain,
    ( ~ l1_struct_0(X0_55)
    | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1399,plain,
    ( u1_struct_0(X0_55) = k2_struct_0(X0_55)
    | l1_struct_0(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_2298,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_1405,c_1399])).

cnf(c_599,plain,
    ( l1_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_550])).

cnf(c_600,plain,
    ( l1_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_1150,plain,
    ( l1_struct_0(sK9) ),
    inference(subtyping,[status(esa)],[c_600])).

cnf(c_1406,plain,
    ( l1_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1150])).

cnf(c_1661,plain,
    ( u1_struct_0(sK9) = k2_struct_0(sK9) ),
    inference(superposition,[status(thm)],[c_1406,c_1399])).

cnf(c_22,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1155,plain,
    ( ~ r1_tsep_1(X0_55,X1_55)
    | r1_xboole_0(u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ l1_struct_0(X0_55)
    | ~ l1_struct_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1401,plain,
    ( r1_tsep_1(X0_55,X1_55) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_55),u1_struct_0(X1_55)) = iProver_top
    | l1_struct_0(X0_55) != iProver_top
    | l1_struct_0(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_2097,plain,
    ( r1_tsep_1(X0_55,sK9) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_55),k2_struct_0(sK9)) = iProver_top
    | l1_struct_0(X0_55) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_1401])).

cnf(c_601,plain,
    ( l1_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_2888,plain,
    ( l1_struct_0(X0_55) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_55),k2_struct_0(sK9)) = iProver_top
    | r1_tsep_1(X0_55,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2097,c_601])).

cnf(c_2889,plain,
    ( r1_tsep_1(X0_55,sK9) != iProver_top
    | r1_xboole_0(u1_struct_0(X0_55),k2_struct_0(sK9)) = iProver_top
    | l1_struct_0(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2888])).

cnf(c_2897,plain,
    ( r1_tsep_1(sK8,sK9) != iProver_top
    | r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2298,c_2889])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1159,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | ~ r2_hidden(X0_56,k3_xboole_0(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1768,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))
    | ~ r2_hidden(X0_56,k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_2583,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))
    | ~ r2_hidden(sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_1768])).

cnf(c_2584,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != iProver_top
    | r2_hidden(sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2583])).

cnf(c_1165,plain,
    ( ~ r2_hidden(X0_56,X0_54)
    | r2_hidden(X1_56,X1_54)
    | X1_56 != X0_56
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_1503,plain,
    ( r2_hidden(X0_56,X0_54)
    | ~ r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8))
    | X0_56 != sK2(u1_struct_0(sK8))
    | X0_54 != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_1607,plain,
    ( r2_hidden(X0_56,k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)))
    | ~ r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8))
    | X0_56 != sK2(u1_struct_0(sK8))
    | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_2170,plain,
    ( r2_hidden(sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)))
    | ~ r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8))
    | sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))) != sK2(u1_struct_0(sK8))
    | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_2175,plain,
    ( sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))) != sK2(u1_struct_0(sK8))
    | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != u1_struct_0(sK8)
    | r2_hidden(sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))) = iProver_top
    | r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2170])).

cnf(c_1164,plain,
    ( sK2(X0_54) = sK2(X1_54)
    | X0_54 != X1_54 ),
    theory(equality)).

cnf(c_1669,plain,
    ( sK2(X0_54) = sK2(u1_struct_0(sK8))
    | X0_54 != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_2010,plain,
    ( sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))) = sK2(u1_struct_0(sK8))
    | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_24,negated_conjecture,
    ( r1_tsep_1(sK8,sK9)
    | r1_tsep_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1153,negated_conjecture,
    ( r1_tsep_1(sK8,sK9)
    | r1_tsep_1(sK9,sK8) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1403,plain,
    ( r1_tsep_1(sK8,sK9) = iProver_top
    | r1_tsep_1(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_23,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1154,plain,
    ( ~ r1_tsep_1(X0_55,X1_55)
    | r1_tsep_1(X1_55,X0_55)
    | ~ l1_struct_0(X0_55)
    | ~ l1_struct_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1402,plain,
    ( r1_tsep_1(X0_55,X1_55) != iProver_top
    | r1_tsep_1(X1_55,X0_55) = iProver_top
    | l1_struct_0(X0_55) != iProver_top
    | l1_struct_0(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_1815,plain,
    ( r1_tsep_1(sK9,sK8) = iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1402])).

cnf(c_33,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_51,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_53,plain,
    ( l1_pre_topc(sK8) != iProver_top
    | l1_struct_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_528,plain,
    ( l1_pre_topc(sK8) = iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_549,plain,
    ( l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_1818,plain,
    ( r1_tsep_1(sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1815,c_33,c_53,c_528,c_549,c_601])).

cnf(c_1823,plain,
    ( r1_tsep_1(sK8,sK9) = iProver_top
    | l1_struct_0(sK8) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1818,c_1402])).

cnf(c_1163,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_1524,plain,
    ( X0_54 != X1_54
    | X0_54 = u1_struct_0(sK8)
    | u1_struct_0(sK8) != X1_54 ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_1563,plain,
    ( X0_54 = u1_struct_0(sK8)
    | X0_54 != k2_struct_0(sK8)
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_1595,plain,
    ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = u1_struct_0(sK8)
    | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != k2_struct_0(sK8)
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_1594,plain,
    ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = u1_struct_0(sK8)
    | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) != k2_struct_0(sK8)
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_622,plain,
    ( ~ sP0(X0,X1)
    | k3_xboole_0(X2,X3) = X2
    | k2_struct_0(X1) != X3
    | k2_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_623,plain,
    ( ~ sP0(X0,X1)
    | k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_17,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_412,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_17,c_6])).

cnf(c_416,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_19])).

cnf(c_417,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_416])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK8,sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_562,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_417,c_28])).

cnf(c_563,plain,
    ( sP0(sK8,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_565,plain,
    ( sP0(sK8,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_30])).

cnf(c_829,plain,
    ( k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
    | sK7 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_623,c_565])).

cnf(c_830,plain,
    ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_1144,plain,
    ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8) ),
    inference(subtyping,[status(esa)],[c_830])).

cnf(c_516,plain,
    ( sP0(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK8 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_417,c_25])).

cnf(c_517,plain,
    ( sP0(sK8,sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_557,plain,
    ( sP0(sK8,sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_550,c_517])).

cnf(c_819,plain,
    ( k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
    | sK8 != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_623,c_557])).

cnf(c_820,plain,
    ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = k2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_1146,plain,
    ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = k2_struct_0(sK8) ),
    inference(subtyping,[status(esa)],[c_820])).

cnf(c_1182,plain,
    ( ~ l1_struct_0(sK8)
    | u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_0,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_354,plain,
    ( r2_hidden(sK2(X0),X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | u1_struct_0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_355,plain,
    ( r2_hidden(sK2(u1_struct_0(X0)),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_356,plain,
    ( r2_hidden(sK2(u1_struct_0(X0)),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_358,plain,
    ( r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8)) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | l1_struct_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_52,plain,
    ( ~ l1_pre_topc(sK8)
    | l1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2897,c_2584,c_2175,c_2010,c_1823,c_1595,c_1594,c_1144,c_1146,c_1182,c_601,c_549,c_548,c_528,c_527,c_358,c_53,c_52,c_34,c_33,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.50/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.05  
% 1.50/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.50/1.05  
% 1.50/1.05  ------  iProver source info
% 1.50/1.05  
% 1.50/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.50/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.50/1.05  git: non_committed_changes: false
% 1.50/1.05  git: last_make_outside_of_git: false
% 1.50/1.05  
% 1.50/1.05  ------ 
% 1.50/1.05  
% 1.50/1.05  ------ Input Options
% 1.50/1.05  
% 1.50/1.05  --out_options                           all
% 1.50/1.05  --tptp_safe_out                         true
% 1.50/1.05  --problem_path                          ""
% 1.50/1.05  --include_path                          ""
% 1.50/1.05  --clausifier                            res/vclausify_rel
% 1.50/1.05  --clausifier_options                    --mode clausify
% 1.50/1.05  --stdin                                 false
% 1.50/1.05  --stats_out                             all
% 1.50/1.05  
% 1.50/1.05  ------ General Options
% 1.50/1.05  
% 1.50/1.05  --fof                                   false
% 1.50/1.05  --time_out_real                         305.
% 1.50/1.05  --time_out_virtual                      -1.
% 1.50/1.05  --symbol_type_check                     false
% 1.50/1.05  --clausify_out                          false
% 1.50/1.05  --sig_cnt_out                           false
% 1.50/1.05  --trig_cnt_out                          false
% 1.50/1.05  --trig_cnt_out_tolerance                1.
% 1.50/1.05  --trig_cnt_out_sk_spl                   false
% 1.50/1.05  --abstr_cl_out                          false
% 1.50/1.05  
% 1.50/1.05  ------ Global Options
% 1.50/1.05  
% 1.50/1.05  --schedule                              default
% 1.50/1.05  --add_important_lit                     false
% 1.50/1.05  --prop_solver_per_cl                    1000
% 1.50/1.05  --min_unsat_core                        false
% 1.50/1.05  --soft_assumptions                      false
% 1.50/1.05  --soft_lemma_size                       3
% 1.50/1.05  --prop_impl_unit_size                   0
% 1.50/1.05  --prop_impl_unit                        []
% 1.50/1.05  --share_sel_clauses                     true
% 1.50/1.05  --reset_solvers                         false
% 1.50/1.05  --bc_imp_inh                            [conj_cone]
% 1.50/1.05  --conj_cone_tolerance                   3.
% 1.50/1.05  --extra_neg_conj                        none
% 1.50/1.05  --large_theory_mode                     true
% 1.50/1.05  --prolific_symb_bound                   200
% 1.50/1.05  --lt_threshold                          2000
% 1.50/1.05  --clause_weak_htbl                      true
% 1.50/1.05  --gc_record_bc_elim                     false
% 1.50/1.05  
% 1.50/1.05  ------ Preprocessing Options
% 1.50/1.05  
% 1.50/1.05  --preprocessing_flag                    true
% 1.50/1.05  --time_out_prep_mult                    0.1
% 1.50/1.05  --splitting_mode                        input
% 1.50/1.05  --splitting_grd                         true
% 1.50/1.05  --splitting_cvd                         false
% 1.50/1.05  --splitting_cvd_svl                     false
% 1.50/1.05  --splitting_nvd                         32
% 1.50/1.05  --sub_typing                            true
% 1.50/1.05  --prep_gs_sim                           true
% 1.50/1.05  --prep_unflatten                        true
% 1.50/1.05  --prep_res_sim                          true
% 1.50/1.05  --prep_upred                            true
% 1.50/1.05  --prep_sem_filter                       exhaustive
% 1.50/1.05  --prep_sem_filter_out                   false
% 1.50/1.05  --pred_elim                             true
% 1.50/1.05  --res_sim_input                         true
% 1.50/1.05  --eq_ax_congr_red                       true
% 1.50/1.05  --pure_diseq_elim                       true
% 1.50/1.05  --brand_transform                       false
% 1.50/1.05  --non_eq_to_eq                          false
% 1.50/1.05  --prep_def_merge                        true
% 1.50/1.05  --prep_def_merge_prop_impl              false
% 1.50/1.05  --prep_def_merge_mbd                    true
% 1.50/1.05  --prep_def_merge_tr_red                 false
% 1.50/1.05  --prep_def_merge_tr_cl                  false
% 1.50/1.05  --smt_preprocessing                     true
% 1.50/1.05  --smt_ac_axioms                         fast
% 1.50/1.05  --preprocessed_out                      false
% 1.50/1.05  --preprocessed_stats                    false
% 1.50/1.05  
% 1.50/1.05  ------ Abstraction refinement Options
% 1.50/1.05  
% 1.50/1.05  --abstr_ref                             []
% 1.50/1.05  --abstr_ref_prep                        false
% 1.50/1.05  --abstr_ref_until_sat                   false
% 1.50/1.05  --abstr_ref_sig_restrict                funpre
% 1.50/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/1.05  --abstr_ref_under                       []
% 1.50/1.05  
% 1.50/1.05  ------ SAT Options
% 1.50/1.05  
% 1.50/1.05  --sat_mode                              false
% 1.50/1.05  --sat_fm_restart_options                ""
% 1.50/1.05  --sat_gr_def                            false
% 1.50/1.05  --sat_epr_types                         true
% 1.50/1.05  --sat_non_cyclic_types                  false
% 1.50/1.05  --sat_finite_models                     false
% 1.50/1.05  --sat_fm_lemmas                         false
% 1.50/1.05  --sat_fm_prep                           false
% 1.50/1.05  --sat_fm_uc_incr                        true
% 1.50/1.05  --sat_out_model                         small
% 1.50/1.05  --sat_out_clauses                       false
% 1.50/1.05  
% 1.50/1.05  ------ QBF Options
% 1.50/1.05  
% 1.50/1.05  --qbf_mode                              false
% 1.50/1.05  --qbf_elim_univ                         false
% 1.50/1.05  --qbf_dom_inst                          none
% 1.50/1.05  --qbf_dom_pre_inst                      false
% 1.50/1.05  --qbf_sk_in                             false
% 1.50/1.05  --qbf_pred_elim                         true
% 1.50/1.05  --qbf_split                             512
% 1.50/1.05  
% 1.50/1.05  ------ BMC1 Options
% 1.50/1.05  
% 1.50/1.05  --bmc1_incremental                      false
% 1.50/1.05  --bmc1_axioms                           reachable_all
% 1.50/1.05  --bmc1_min_bound                        0
% 1.50/1.05  --bmc1_max_bound                        -1
% 1.50/1.05  --bmc1_max_bound_default                -1
% 1.50/1.05  --bmc1_symbol_reachability              true
% 1.50/1.05  --bmc1_property_lemmas                  false
% 1.50/1.05  --bmc1_k_induction                      false
% 1.50/1.05  --bmc1_non_equiv_states                 false
% 1.50/1.05  --bmc1_deadlock                         false
% 1.50/1.05  --bmc1_ucm                              false
% 1.50/1.05  --bmc1_add_unsat_core                   none
% 1.50/1.05  --bmc1_unsat_core_children              false
% 1.50/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/1.05  --bmc1_out_stat                         full
% 1.50/1.05  --bmc1_ground_init                      false
% 1.50/1.05  --bmc1_pre_inst_next_state              false
% 1.50/1.05  --bmc1_pre_inst_state                   false
% 1.50/1.05  --bmc1_pre_inst_reach_state             false
% 1.50/1.05  --bmc1_out_unsat_core                   false
% 1.50/1.05  --bmc1_aig_witness_out                  false
% 1.50/1.05  --bmc1_verbose                          false
% 1.50/1.05  --bmc1_dump_clauses_tptp                false
% 1.50/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.50/1.05  --bmc1_dump_file                        -
% 1.50/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.50/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.50/1.05  --bmc1_ucm_extend_mode                  1
% 1.50/1.05  --bmc1_ucm_init_mode                    2
% 1.50/1.05  --bmc1_ucm_cone_mode                    none
% 1.50/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.50/1.05  --bmc1_ucm_relax_model                  4
% 1.50/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.50/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/1.05  --bmc1_ucm_layered_model                none
% 1.50/1.05  --bmc1_ucm_max_lemma_size               10
% 1.50/1.05  
% 1.50/1.05  ------ AIG Options
% 1.50/1.05  
% 1.50/1.05  --aig_mode                              false
% 1.50/1.05  
% 1.50/1.05  ------ Instantiation Options
% 1.50/1.05  
% 1.50/1.05  --instantiation_flag                    true
% 1.50/1.05  --inst_sos_flag                         false
% 1.50/1.05  --inst_sos_phase                        true
% 1.50/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/1.05  --inst_lit_sel_side                     num_symb
% 1.50/1.05  --inst_solver_per_active                1400
% 1.50/1.05  --inst_solver_calls_frac                1.
% 1.50/1.05  --inst_passive_queue_type               priority_queues
% 1.50/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/1.05  --inst_passive_queues_freq              [25;2]
% 1.50/1.05  --inst_dismatching                      true
% 1.50/1.05  --inst_eager_unprocessed_to_passive     true
% 1.50/1.05  --inst_prop_sim_given                   true
% 1.50/1.05  --inst_prop_sim_new                     false
% 1.50/1.05  --inst_subs_new                         false
% 1.50/1.05  --inst_eq_res_simp                      false
% 1.50/1.05  --inst_subs_given                       false
% 1.50/1.05  --inst_orphan_elimination               true
% 1.50/1.05  --inst_learning_loop_flag               true
% 1.50/1.05  --inst_learning_start                   3000
% 1.50/1.05  --inst_learning_factor                  2
% 1.50/1.05  --inst_start_prop_sim_after_learn       3
% 1.50/1.05  --inst_sel_renew                        solver
% 1.50/1.05  --inst_lit_activity_flag                true
% 1.50/1.05  --inst_restr_to_given                   false
% 1.50/1.05  --inst_activity_threshold               500
% 1.50/1.05  --inst_out_proof                        true
% 1.50/1.05  
% 1.50/1.05  ------ Resolution Options
% 1.50/1.05  
% 1.50/1.05  --resolution_flag                       true
% 1.50/1.05  --res_lit_sel                           adaptive
% 1.50/1.05  --res_lit_sel_side                      none
% 1.50/1.05  --res_ordering                          kbo
% 1.50/1.05  --res_to_prop_solver                    active
% 1.50/1.05  --res_prop_simpl_new                    false
% 1.50/1.05  --res_prop_simpl_given                  true
% 1.50/1.05  --res_passive_queue_type                priority_queues
% 1.50/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/1.05  --res_passive_queues_freq               [15;5]
% 1.50/1.05  --res_forward_subs                      full
% 1.50/1.05  --res_backward_subs                     full
% 1.50/1.05  --res_forward_subs_resolution           true
% 1.50/1.05  --res_backward_subs_resolution          true
% 1.50/1.05  --res_orphan_elimination                true
% 1.50/1.05  --res_time_limit                        2.
% 1.50/1.05  --res_out_proof                         true
% 1.50/1.05  
% 1.50/1.05  ------ Superposition Options
% 1.50/1.05  
% 1.50/1.05  --superposition_flag                    true
% 1.50/1.05  --sup_passive_queue_type                priority_queues
% 1.50/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.50/1.05  --demod_completeness_check              fast
% 1.50/1.05  --demod_use_ground                      true
% 1.50/1.05  --sup_to_prop_solver                    passive
% 1.50/1.05  --sup_prop_simpl_new                    true
% 1.50/1.05  --sup_prop_simpl_given                  true
% 1.50/1.05  --sup_fun_splitting                     false
% 1.50/1.05  --sup_smt_interval                      50000
% 1.50/1.05  
% 1.50/1.05  ------ Superposition Simplification Setup
% 1.50/1.05  
% 1.50/1.05  --sup_indices_passive                   []
% 1.50/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.05  --sup_full_bw                           [BwDemod]
% 1.50/1.05  --sup_immed_triv                        [TrivRules]
% 1.50/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.05  --sup_immed_bw_main                     []
% 1.50/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/1.05  
% 1.50/1.05  ------ Combination Options
% 1.50/1.05  
% 1.50/1.05  --comb_res_mult                         3
% 1.50/1.05  --comb_sup_mult                         2
% 1.50/1.05  --comb_inst_mult                        10
% 1.50/1.05  
% 1.50/1.05  ------ Debug Options
% 1.50/1.05  
% 1.50/1.05  --dbg_backtrace                         false
% 1.50/1.05  --dbg_dump_prop_clauses                 false
% 1.50/1.05  --dbg_dump_prop_clauses_file            -
% 1.50/1.05  --dbg_out_stat                          false
% 1.50/1.05  ------ Parsing...
% 1.50/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.50/1.05  
% 1.50/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.50/1.05  
% 1.50/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.50/1.05  
% 1.50/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.50/1.05  ------ Proving...
% 1.50/1.05  ------ Problem Properties 
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  clauses                                 16
% 1.50/1.05  conjectures                             1
% 1.50/1.05  EPR                                     5
% 1.50/1.05  Horn                                    14
% 1.50/1.05  unary                                   9
% 1.50/1.05  binary                                  4
% 1.50/1.05  lits                                    29
% 1.50/1.05  lits eq                                 4
% 1.50/1.05  fd_pure                                 0
% 1.50/1.05  fd_pseudo                               0
% 1.50/1.05  fd_cond                                 0
% 1.50/1.05  fd_pseudo_cond                          0
% 1.50/1.05  AC symbols                              0
% 1.50/1.05  
% 1.50/1.05  ------ Schedule dynamic 5 is on 
% 1.50/1.05  
% 1.50/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  ------ 
% 1.50/1.05  Current options:
% 1.50/1.05  ------ 
% 1.50/1.05  
% 1.50/1.05  ------ Input Options
% 1.50/1.05  
% 1.50/1.05  --out_options                           all
% 1.50/1.05  --tptp_safe_out                         true
% 1.50/1.05  --problem_path                          ""
% 1.50/1.05  --include_path                          ""
% 1.50/1.05  --clausifier                            res/vclausify_rel
% 1.50/1.05  --clausifier_options                    --mode clausify
% 1.50/1.05  --stdin                                 false
% 1.50/1.05  --stats_out                             all
% 1.50/1.05  
% 1.50/1.05  ------ General Options
% 1.50/1.05  
% 1.50/1.05  --fof                                   false
% 1.50/1.05  --time_out_real                         305.
% 1.50/1.05  --time_out_virtual                      -1.
% 1.50/1.05  --symbol_type_check                     false
% 1.50/1.05  --clausify_out                          false
% 1.50/1.05  --sig_cnt_out                           false
% 1.50/1.05  --trig_cnt_out                          false
% 1.50/1.05  --trig_cnt_out_tolerance                1.
% 1.50/1.05  --trig_cnt_out_sk_spl                   false
% 1.50/1.05  --abstr_cl_out                          false
% 1.50/1.05  
% 1.50/1.05  ------ Global Options
% 1.50/1.05  
% 1.50/1.05  --schedule                              default
% 1.50/1.05  --add_important_lit                     false
% 1.50/1.05  --prop_solver_per_cl                    1000
% 1.50/1.05  --min_unsat_core                        false
% 1.50/1.05  --soft_assumptions                      false
% 1.50/1.05  --soft_lemma_size                       3
% 1.50/1.05  --prop_impl_unit_size                   0
% 1.50/1.05  --prop_impl_unit                        []
% 1.50/1.05  --share_sel_clauses                     true
% 1.50/1.05  --reset_solvers                         false
% 1.50/1.05  --bc_imp_inh                            [conj_cone]
% 1.50/1.05  --conj_cone_tolerance                   3.
% 1.50/1.05  --extra_neg_conj                        none
% 1.50/1.05  --large_theory_mode                     true
% 1.50/1.05  --prolific_symb_bound                   200
% 1.50/1.05  --lt_threshold                          2000
% 1.50/1.05  --clause_weak_htbl                      true
% 1.50/1.05  --gc_record_bc_elim                     false
% 1.50/1.05  
% 1.50/1.05  ------ Preprocessing Options
% 1.50/1.05  
% 1.50/1.05  --preprocessing_flag                    true
% 1.50/1.05  --time_out_prep_mult                    0.1
% 1.50/1.05  --splitting_mode                        input
% 1.50/1.05  --splitting_grd                         true
% 1.50/1.05  --splitting_cvd                         false
% 1.50/1.05  --splitting_cvd_svl                     false
% 1.50/1.05  --splitting_nvd                         32
% 1.50/1.05  --sub_typing                            true
% 1.50/1.05  --prep_gs_sim                           true
% 1.50/1.05  --prep_unflatten                        true
% 1.50/1.05  --prep_res_sim                          true
% 1.50/1.05  --prep_upred                            true
% 1.50/1.05  --prep_sem_filter                       exhaustive
% 1.50/1.05  --prep_sem_filter_out                   false
% 1.50/1.05  --pred_elim                             true
% 1.50/1.05  --res_sim_input                         true
% 1.50/1.05  --eq_ax_congr_red                       true
% 1.50/1.05  --pure_diseq_elim                       true
% 1.50/1.05  --brand_transform                       false
% 1.50/1.05  --non_eq_to_eq                          false
% 1.50/1.05  --prep_def_merge                        true
% 1.50/1.05  --prep_def_merge_prop_impl              false
% 1.50/1.05  --prep_def_merge_mbd                    true
% 1.50/1.05  --prep_def_merge_tr_red                 false
% 1.50/1.05  --prep_def_merge_tr_cl                  false
% 1.50/1.05  --smt_preprocessing                     true
% 1.50/1.05  --smt_ac_axioms                         fast
% 1.50/1.05  --preprocessed_out                      false
% 1.50/1.05  --preprocessed_stats                    false
% 1.50/1.05  
% 1.50/1.05  ------ Abstraction refinement Options
% 1.50/1.05  
% 1.50/1.05  --abstr_ref                             []
% 1.50/1.05  --abstr_ref_prep                        false
% 1.50/1.05  --abstr_ref_until_sat                   false
% 1.50/1.05  --abstr_ref_sig_restrict                funpre
% 1.50/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/1.05  --abstr_ref_under                       []
% 1.50/1.05  
% 1.50/1.05  ------ SAT Options
% 1.50/1.05  
% 1.50/1.05  --sat_mode                              false
% 1.50/1.05  --sat_fm_restart_options                ""
% 1.50/1.05  --sat_gr_def                            false
% 1.50/1.05  --sat_epr_types                         true
% 1.50/1.05  --sat_non_cyclic_types                  false
% 1.50/1.05  --sat_finite_models                     false
% 1.50/1.05  --sat_fm_lemmas                         false
% 1.50/1.05  --sat_fm_prep                           false
% 1.50/1.05  --sat_fm_uc_incr                        true
% 1.50/1.05  --sat_out_model                         small
% 1.50/1.05  --sat_out_clauses                       false
% 1.50/1.05  
% 1.50/1.05  ------ QBF Options
% 1.50/1.05  
% 1.50/1.05  --qbf_mode                              false
% 1.50/1.05  --qbf_elim_univ                         false
% 1.50/1.05  --qbf_dom_inst                          none
% 1.50/1.05  --qbf_dom_pre_inst                      false
% 1.50/1.05  --qbf_sk_in                             false
% 1.50/1.05  --qbf_pred_elim                         true
% 1.50/1.05  --qbf_split                             512
% 1.50/1.05  
% 1.50/1.05  ------ BMC1 Options
% 1.50/1.05  
% 1.50/1.05  --bmc1_incremental                      false
% 1.50/1.05  --bmc1_axioms                           reachable_all
% 1.50/1.05  --bmc1_min_bound                        0
% 1.50/1.05  --bmc1_max_bound                        -1
% 1.50/1.05  --bmc1_max_bound_default                -1
% 1.50/1.05  --bmc1_symbol_reachability              true
% 1.50/1.05  --bmc1_property_lemmas                  false
% 1.50/1.05  --bmc1_k_induction                      false
% 1.50/1.05  --bmc1_non_equiv_states                 false
% 1.50/1.05  --bmc1_deadlock                         false
% 1.50/1.05  --bmc1_ucm                              false
% 1.50/1.05  --bmc1_add_unsat_core                   none
% 1.50/1.05  --bmc1_unsat_core_children              false
% 1.50/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/1.05  --bmc1_out_stat                         full
% 1.50/1.05  --bmc1_ground_init                      false
% 1.50/1.05  --bmc1_pre_inst_next_state              false
% 1.50/1.05  --bmc1_pre_inst_state                   false
% 1.50/1.05  --bmc1_pre_inst_reach_state             false
% 1.50/1.05  --bmc1_out_unsat_core                   false
% 1.50/1.05  --bmc1_aig_witness_out                  false
% 1.50/1.05  --bmc1_verbose                          false
% 1.50/1.05  --bmc1_dump_clauses_tptp                false
% 1.50/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.50/1.05  --bmc1_dump_file                        -
% 1.50/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.50/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.50/1.05  --bmc1_ucm_extend_mode                  1
% 1.50/1.05  --bmc1_ucm_init_mode                    2
% 1.50/1.05  --bmc1_ucm_cone_mode                    none
% 1.50/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.50/1.05  --bmc1_ucm_relax_model                  4
% 1.50/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.50/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/1.05  --bmc1_ucm_layered_model                none
% 1.50/1.05  --bmc1_ucm_max_lemma_size               10
% 1.50/1.05  
% 1.50/1.05  ------ AIG Options
% 1.50/1.05  
% 1.50/1.05  --aig_mode                              false
% 1.50/1.05  
% 1.50/1.05  ------ Instantiation Options
% 1.50/1.05  
% 1.50/1.05  --instantiation_flag                    true
% 1.50/1.05  --inst_sos_flag                         false
% 1.50/1.05  --inst_sos_phase                        true
% 1.50/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/1.05  --inst_lit_sel_side                     none
% 1.50/1.05  --inst_solver_per_active                1400
% 1.50/1.05  --inst_solver_calls_frac                1.
% 1.50/1.05  --inst_passive_queue_type               priority_queues
% 1.50/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/1.05  --inst_passive_queues_freq              [25;2]
% 1.50/1.05  --inst_dismatching                      true
% 1.50/1.05  --inst_eager_unprocessed_to_passive     true
% 1.50/1.05  --inst_prop_sim_given                   true
% 1.50/1.05  --inst_prop_sim_new                     false
% 1.50/1.05  --inst_subs_new                         false
% 1.50/1.05  --inst_eq_res_simp                      false
% 1.50/1.05  --inst_subs_given                       false
% 1.50/1.05  --inst_orphan_elimination               true
% 1.50/1.05  --inst_learning_loop_flag               true
% 1.50/1.05  --inst_learning_start                   3000
% 1.50/1.05  --inst_learning_factor                  2
% 1.50/1.05  --inst_start_prop_sim_after_learn       3
% 1.50/1.05  --inst_sel_renew                        solver
% 1.50/1.05  --inst_lit_activity_flag                true
% 1.50/1.05  --inst_restr_to_given                   false
% 1.50/1.05  --inst_activity_threshold               500
% 1.50/1.05  --inst_out_proof                        true
% 1.50/1.05  
% 1.50/1.05  ------ Resolution Options
% 1.50/1.05  
% 1.50/1.05  --resolution_flag                       false
% 1.50/1.05  --res_lit_sel                           adaptive
% 1.50/1.05  --res_lit_sel_side                      none
% 1.50/1.05  --res_ordering                          kbo
% 1.50/1.05  --res_to_prop_solver                    active
% 1.50/1.05  --res_prop_simpl_new                    false
% 1.50/1.05  --res_prop_simpl_given                  true
% 1.50/1.05  --res_passive_queue_type                priority_queues
% 1.50/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/1.05  --res_passive_queues_freq               [15;5]
% 1.50/1.05  --res_forward_subs                      full
% 1.50/1.05  --res_backward_subs                     full
% 1.50/1.05  --res_forward_subs_resolution           true
% 1.50/1.05  --res_backward_subs_resolution          true
% 1.50/1.05  --res_orphan_elimination                true
% 1.50/1.05  --res_time_limit                        2.
% 1.50/1.05  --res_out_proof                         true
% 1.50/1.05  
% 1.50/1.05  ------ Superposition Options
% 1.50/1.05  
% 1.50/1.05  --superposition_flag                    true
% 1.50/1.05  --sup_passive_queue_type                priority_queues
% 1.50/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.50/1.05  --demod_completeness_check              fast
% 1.50/1.05  --demod_use_ground                      true
% 1.50/1.05  --sup_to_prop_solver                    passive
% 1.50/1.05  --sup_prop_simpl_new                    true
% 1.50/1.05  --sup_prop_simpl_given                  true
% 1.50/1.05  --sup_fun_splitting                     false
% 1.50/1.05  --sup_smt_interval                      50000
% 1.50/1.05  
% 1.50/1.05  ------ Superposition Simplification Setup
% 1.50/1.05  
% 1.50/1.05  --sup_indices_passive                   []
% 1.50/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.05  --sup_full_bw                           [BwDemod]
% 1.50/1.05  --sup_immed_triv                        [TrivRules]
% 1.50/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.05  --sup_immed_bw_main                     []
% 1.50/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/1.05  
% 1.50/1.05  ------ Combination Options
% 1.50/1.05  
% 1.50/1.05  --comb_res_mult                         3
% 1.50/1.05  --comb_sup_mult                         2
% 1.50/1.05  --comb_inst_mult                        10
% 1.50/1.05  
% 1.50/1.05  ------ Debug Options
% 1.50/1.05  
% 1.50/1.05  --dbg_backtrace                         false
% 1.50/1.05  --dbg_dump_prop_clauses                 false
% 1.50/1.05  --dbg_dump_prop_clauses_file            -
% 1.50/1.05  --dbg_out_stat                          false
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  ------ Proving...
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  % SZS status Theorem for theBenchmark.p
% 1.50/1.05  
% 1.50/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.50/1.05  
% 1.50/1.05  fof(f6,axiom,(
% 1.50/1.05    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f21,plain,(
% 1.50/1.05    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.50/1.05    inference(ennf_transformation,[],[f6])).
% 1.50/1.05  
% 1.50/1.05  fof(f68,plain,(
% 1.50/1.05    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f21])).
% 1.50/1.05  
% 1.50/1.05  fof(f7,axiom,(
% 1.50/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f22,plain,(
% 1.50/1.05    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.50/1.05    inference(ennf_transformation,[],[f7])).
% 1.50/1.05  
% 1.50/1.05  fof(f69,plain,(
% 1.50/1.05    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f22])).
% 1.50/1.05  
% 1.50/1.05  fof(f11,conjecture,(
% 1.50/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f12,negated_conjecture,(
% 1.50/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.50/1.05    inference(negated_conjecture,[],[f11])).
% 1.50/1.05  
% 1.50/1.05  fof(f15,plain,(
% 1.50/1.05    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.50/1.05    inference(pure_predicate_removal,[],[f12])).
% 1.50/1.05  
% 1.50/1.05  fof(f28,plain,(
% 1.50/1.05    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.50/1.05    inference(ennf_transformation,[],[f15])).
% 1.50/1.05  
% 1.50/1.05  fof(f29,plain,(
% 1.50/1.05    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.50/1.05    inference(flattening,[],[f28])).
% 1.50/1.05  
% 1.50/1.05  fof(f48,plain,(
% 1.50/1.05    ( ! [X0,X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK9,X1) | r1_tsep_1(X1,sK9)) & m1_pre_topc(X1,sK9) & m1_pre_topc(sK9,X0) & ~v2_struct_0(sK9))) )),
% 1.50/1.05    introduced(choice_axiom,[])).
% 1.50/1.05  
% 1.50/1.05  fof(f47,plain,(
% 1.50/1.05    ( ! [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK8) | r1_tsep_1(sK8,X2)) & m1_pre_topc(sK8,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK8,X0) & ~v2_struct_0(sK8))) )),
% 1.50/1.05    introduced(choice_axiom,[])).
% 1.50/1.05  
% 1.50/1.05  fof(f46,plain,(
% 1.50/1.05    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK7) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK7) & ~v2_struct_0(X1)) & l1_pre_topc(sK7) & ~v2_struct_0(sK7))),
% 1.50/1.05    introduced(choice_axiom,[])).
% 1.50/1.05  
% 1.50/1.05  fof(f49,plain,(
% 1.50/1.05    (((r1_tsep_1(sK9,sK8) | r1_tsep_1(sK8,sK9)) & m1_pre_topc(sK8,sK9) & m1_pre_topc(sK9,sK7) & ~v2_struct_0(sK9)) & m1_pre_topc(sK8,sK7) & ~v2_struct_0(sK8)) & l1_pre_topc(sK7) & ~v2_struct_0(sK7)),
% 1.50/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f29,f48,f47,f46])).
% 1.50/1.05  
% 1.50/1.05  fof(f79,plain,(
% 1.50/1.05    m1_pre_topc(sK9,sK7)),
% 1.50/1.05    inference(cnf_transformation,[],[f49])).
% 1.50/1.05  
% 1.50/1.05  fof(f75,plain,(
% 1.50/1.05    l1_pre_topc(sK7)),
% 1.50/1.05    inference(cnf_transformation,[],[f49])).
% 1.50/1.05  
% 1.50/1.05  fof(f80,plain,(
% 1.50/1.05    m1_pre_topc(sK8,sK9)),
% 1.50/1.05    inference(cnf_transformation,[],[f49])).
% 1.50/1.05  
% 1.50/1.05  fof(f4,axiom,(
% 1.50/1.05    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f19,plain,(
% 1.50/1.05    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.50/1.05    inference(ennf_transformation,[],[f4])).
% 1.50/1.05  
% 1.50/1.05  fof(f54,plain,(
% 1.50/1.05    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f19])).
% 1.50/1.05  
% 1.50/1.05  fof(f9,axiom,(
% 1.50/1.05    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f25,plain,(
% 1.50/1.05    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.50/1.05    inference(ennf_transformation,[],[f9])).
% 1.50/1.05  
% 1.50/1.05  fof(f45,plain,(
% 1.50/1.05    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.50/1.05    inference(nnf_transformation,[],[f25])).
% 1.50/1.05  
% 1.50/1.05  fof(f71,plain,(
% 1.50/1.05    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f45])).
% 1.50/1.05  
% 1.50/1.05  fof(f2,axiom,(
% 1.50/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f13,plain,(
% 1.50/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.50/1.05    inference(rectify,[],[f2])).
% 1.50/1.05  
% 1.50/1.05  fof(f17,plain,(
% 1.50/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.50/1.05    inference(ennf_transformation,[],[f13])).
% 1.50/1.05  
% 1.50/1.05  fof(f35,plain,(
% 1.50/1.05    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.50/1.05    introduced(choice_axiom,[])).
% 1.50/1.05  
% 1.50/1.05  fof(f36,plain,(
% 1.50/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.50/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f35])).
% 1.50/1.05  
% 1.50/1.05  fof(f52,plain,(
% 1.50/1.05    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.50/1.05    inference(cnf_transformation,[],[f36])).
% 1.50/1.05  
% 1.50/1.05  fof(f81,plain,(
% 1.50/1.05    r1_tsep_1(sK9,sK8) | r1_tsep_1(sK8,sK9)),
% 1.50/1.05    inference(cnf_transformation,[],[f49])).
% 1.50/1.05  
% 1.50/1.05  fof(f10,axiom,(
% 1.50/1.05    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f26,plain,(
% 1.50/1.05    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.50/1.05    inference(ennf_transformation,[],[f10])).
% 1.50/1.05  
% 1.50/1.05  fof(f27,plain,(
% 1.50/1.05    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.50/1.05    inference(flattening,[],[f26])).
% 1.50/1.05  
% 1.50/1.05  fof(f73,plain,(
% 1.50/1.05    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f27])).
% 1.50/1.05  
% 1.50/1.05  fof(f3,axiom,(
% 1.50/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f18,plain,(
% 1.50/1.05    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.50/1.05    inference(ennf_transformation,[],[f3])).
% 1.50/1.05  
% 1.50/1.05  fof(f53,plain,(
% 1.50/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f18])).
% 1.50/1.05  
% 1.50/1.05  fof(f30,plain,(
% 1.50/1.05    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 1.50/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.50/1.05  
% 1.50/1.05  fof(f38,plain,(
% 1.50/1.05    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 1.50/1.05    inference(nnf_transformation,[],[f30])).
% 1.50/1.05  
% 1.50/1.05  fof(f39,plain,(
% 1.50/1.05    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 1.50/1.05    inference(flattening,[],[f38])).
% 1.50/1.05  
% 1.50/1.05  fof(f40,plain,(
% 1.50/1.05    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 1.50/1.05    inference(rectify,[],[f39])).
% 1.50/1.05  
% 1.50/1.05  fof(f43,plain,(
% 1.50/1.05    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.50/1.05    introduced(choice_axiom,[])).
% 1.50/1.05  
% 1.50/1.05  fof(f42,plain,(
% 1.50/1.05    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 1.50/1.05    introduced(choice_axiom,[])).
% 1.50/1.05  
% 1.50/1.05  fof(f41,plain,(
% 1.50/1.05    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.50/1.05    introduced(choice_axiom,[])).
% 1.50/1.05  
% 1.50/1.05  fof(f44,plain,(
% 1.50/1.05    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 1.50/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f43,f42,f41])).
% 1.50/1.05  
% 1.50/1.05  fof(f57,plain,(
% 1.50/1.05    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f44])).
% 1.50/1.05  
% 1.50/1.05  fof(f5,axiom,(
% 1.50/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f20,plain,(
% 1.50/1.05    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.50/1.05    inference(ennf_transformation,[],[f5])).
% 1.50/1.05  
% 1.50/1.05  fof(f31,plain,(
% 1.50/1.05    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.50/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.50/1.05  
% 1.50/1.05  fof(f32,plain,(
% 1.50/1.05    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.50/1.05    inference(definition_folding,[],[f20,f31,f30])).
% 1.50/1.05  
% 1.50/1.05  fof(f67,plain,(
% 1.50/1.05    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f32])).
% 1.50/1.05  
% 1.50/1.05  fof(f37,plain,(
% 1.50/1.05    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 1.50/1.05    inference(nnf_transformation,[],[f31])).
% 1.50/1.05  
% 1.50/1.05  fof(f55,plain,(
% 1.50/1.05    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f37])).
% 1.50/1.05  
% 1.50/1.05  fof(f77,plain,(
% 1.50/1.05    m1_pre_topc(sK8,sK7)),
% 1.50/1.05    inference(cnf_transformation,[],[f49])).
% 1.50/1.05  
% 1.50/1.05  fof(f1,axiom,(
% 1.50/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f14,plain,(
% 1.50/1.05    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.50/1.05    inference(unused_predicate_definition_removal,[],[f1])).
% 1.50/1.05  
% 1.50/1.05  fof(f16,plain,(
% 1.50/1.05    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.50/1.05    inference(ennf_transformation,[],[f14])).
% 1.50/1.05  
% 1.50/1.05  fof(f33,plain,(
% 1.50/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.50/1.05    introduced(choice_axiom,[])).
% 1.50/1.05  
% 1.50/1.05  fof(f34,plain,(
% 1.50/1.05    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0))),
% 1.50/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f33])).
% 1.50/1.05  
% 1.50/1.05  fof(f50,plain,(
% 1.50/1.05    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f34])).
% 1.50/1.05  
% 1.50/1.05  fof(f8,axiom,(
% 1.50/1.05    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.50/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.50/1.05  
% 1.50/1.05  fof(f23,plain,(
% 1.50/1.05    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.50/1.05    inference(ennf_transformation,[],[f8])).
% 1.50/1.05  
% 1.50/1.05  fof(f24,plain,(
% 1.50/1.05    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.50/1.05    inference(flattening,[],[f23])).
% 1.50/1.05  
% 1.50/1.05  fof(f70,plain,(
% 1.50/1.05    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.50/1.05    inference(cnf_transformation,[],[f24])).
% 1.50/1.05  
% 1.50/1.05  fof(f76,plain,(
% 1.50/1.05    ~v2_struct_0(sK8)),
% 1.50/1.05    inference(cnf_transformation,[],[f49])).
% 1.50/1.05  
% 1.50/1.05  cnf(c_18,plain,
% 1.50/1.05      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.50/1.05      inference(cnf_transformation,[],[f68]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_19,plain,
% 1.50/1.05      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.50/1.05      inference(cnf_transformation,[],[f69]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_26,negated_conjecture,
% 1.50/1.05      ( m1_pre_topc(sK9,sK7) ),
% 1.50/1.05      inference(cnf_transformation,[],[f79]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_547,plain,
% 1.50/1.05      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK7 != X0 | sK9 != X1 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_548,plain,
% 1.50/1.05      ( ~ l1_pre_topc(sK7) | l1_pre_topc(sK9) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_547]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_30,negated_conjecture,
% 1.50/1.05      ( l1_pre_topc(sK7) ),
% 1.50/1.05      inference(cnf_transformation,[],[f75]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_550,plain,
% 1.50/1.05      ( l1_pre_topc(sK9) ),
% 1.50/1.05      inference(global_propositional_subsumption,
% 1.50/1.05                [status(thm)],
% 1.50/1.05                [c_548,c_30]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_25,negated_conjecture,
% 1.50/1.05      ( m1_pre_topc(sK8,sK9) ),
% 1.50/1.05      inference(cnf_transformation,[],[f80]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_526,plain,
% 1.50/1.05      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK8 != X1 | sK9 != X0 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_527,plain,
% 1.50/1.05      ( l1_pre_topc(sK8) | ~ l1_pre_topc(sK9) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_526]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_558,plain,
% 1.50/1.05      ( l1_pre_topc(sK8) ),
% 1.50/1.05      inference(backward_subsumption_resolution,
% 1.50/1.05                [status(thm)],
% 1.50/1.05                [c_550,c_527]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_592,plain,
% 1.50/1.05      ( l1_struct_0(X0) | sK8 != X0 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_18,c_558]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_593,plain,
% 1.50/1.05      ( l1_struct_0(sK8) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_592]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1151,plain,
% 1.50/1.05      ( l1_struct_0(sK8) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_593]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1405,plain,
% 1.50/1.05      ( l1_struct_0(sK8) = iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_4,plain,
% 1.50/1.05      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.50/1.05      inference(cnf_transformation,[],[f54]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1157,plain,
% 1.50/1.05      ( ~ l1_struct_0(X0_55) | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_4]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1399,plain,
% 1.50/1.05      ( u1_struct_0(X0_55) = k2_struct_0(X0_55)
% 1.50/1.05      | l1_struct_0(X0_55) != iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2298,plain,
% 1.50/1.05      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 1.50/1.05      inference(superposition,[status(thm)],[c_1405,c_1399]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_599,plain,
% 1.50/1.05      ( l1_struct_0(X0) | sK9 != X0 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_18,c_550]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_600,plain,
% 1.50/1.05      ( l1_struct_0(sK9) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_599]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1150,plain,
% 1.50/1.05      ( l1_struct_0(sK9) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_600]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1406,plain,
% 1.50/1.05      ( l1_struct_0(sK9) = iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_1150]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1661,plain,
% 1.50/1.05      ( u1_struct_0(sK9) = k2_struct_0(sK9) ),
% 1.50/1.05      inference(superposition,[status(thm)],[c_1406,c_1399]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_22,plain,
% 1.50/1.05      ( ~ r1_tsep_1(X0,X1)
% 1.50/1.05      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 1.50/1.05      | ~ l1_struct_0(X0)
% 1.50/1.05      | ~ l1_struct_0(X1) ),
% 1.50/1.05      inference(cnf_transformation,[],[f71]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1155,plain,
% 1.50/1.05      ( ~ r1_tsep_1(X0_55,X1_55)
% 1.50/1.05      | r1_xboole_0(u1_struct_0(X0_55),u1_struct_0(X1_55))
% 1.50/1.05      | ~ l1_struct_0(X0_55)
% 1.50/1.05      | ~ l1_struct_0(X1_55) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_22]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1401,plain,
% 1.50/1.05      ( r1_tsep_1(X0_55,X1_55) != iProver_top
% 1.50/1.05      | r1_xboole_0(u1_struct_0(X0_55),u1_struct_0(X1_55)) = iProver_top
% 1.50/1.05      | l1_struct_0(X0_55) != iProver_top
% 1.50/1.05      | l1_struct_0(X1_55) != iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2097,plain,
% 1.50/1.05      ( r1_tsep_1(X0_55,sK9) != iProver_top
% 1.50/1.05      | r1_xboole_0(u1_struct_0(X0_55),k2_struct_0(sK9)) = iProver_top
% 1.50/1.05      | l1_struct_0(X0_55) != iProver_top
% 1.50/1.05      | l1_struct_0(sK9) != iProver_top ),
% 1.50/1.05      inference(superposition,[status(thm)],[c_1661,c_1401]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_601,plain,
% 1.50/1.05      ( l1_struct_0(sK9) = iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2888,plain,
% 1.50/1.05      ( l1_struct_0(X0_55) != iProver_top
% 1.50/1.05      | r1_xboole_0(u1_struct_0(X0_55),k2_struct_0(sK9)) = iProver_top
% 1.50/1.05      | r1_tsep_1(X0_55,sK9) != iProver_top ),
% 1.50/1.05      inference(global_propositional_subsumption,
% 1.50/1.05                [status(thm)],
% 1.50/1.05                [c_2097,c_601]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2889,plain,
% 1.50/1.05      ( r1_tsep_1(X0_55,sK9) != iProver_top
% 1.50/1.05      | r1_xboole_0(u1_struct_0(X0_55),k2_struct_0(sK9)) = iProver_top
% 1.50/1.05      | l1_struct_0(X0_55) != iProver_top ),
% 1.50/1.05      inference(renaming,[status(thm)],[c_2888]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2897,plain,
% 1.50/1.05      ( r1_tsep_1(sK8,sK9) != iProver_top
% 1.50/1.05      | r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = iProver_top
% 1.50/1.05      | l1_struct_0(sK8) != iProver_top ),
% 1.50/1.05      inference(superposition,[status(thm)],[c_2298,c_2889]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1,plain,
% 1.50/1.05      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 1.50/1.05      inference(cnf_transformation,[],[f52]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1159,plain,
% 1.50/1.05      ( ~ r1_xboole_0(X0_54,X1_54)
% 1.50/1.05      | ~ r2_hidden(X0_56,k3_xboole_0(X0_54,X1_54)) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_1]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1768,plain,
% 1.50/1.05      ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))
% 1.50/1.05      | ~ r2_hidden(X0_56,k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1159]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2583,plain,
% 1.50/1.05      ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))
% 1.50/1.05      | ~ r2_hidden(sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1768]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2584,plain,
% 1.50/1.05      ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != iProver_top
% 1.50/1.05      | r2_hidden(sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))) != iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_2583]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1165,plain,
% 1.50/1.05      ( ~ r2_hidden(X0_56,X0_54)
% 1.50/1.05      | r2_hidden(X1_56,X1_54)
% 1.50/1.05      | X1_56 != X0_56
% 1.50/1.05      | X1_54 != X0_54 ),
% 1.50/1.05      theory(equality) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1503,plain,
% 1.50/1.05      ( r2_hidden(X0_56,X0_54)
% 1.50/1.05      | ~ r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8))
% 1.50/1.05      | X0_56 != sK2(u1_struct_0(sK8))
% 1.50/1.05      | X0_54 != u1_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1165]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1607,plain,
% 1.50/1.05      ( r2_hidden(X0_56,k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)))
% 1.50/1.05      | ~ r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8))
% 1.50/1.05      | X0_56 != sK2(u1_struct_0(sK8))
% 1.50/1.05      | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != u1_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1503]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2170,plain,
% 1.50/1.05      ( r2_hidden(sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)))
% 1.50/1.05      | ~ r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8))
% 1.50/1.05      | sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))) != sK2(u1_struct_0(sK8))
% 1.50/1.05      | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != u1_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1607]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2175,plain,
% 1.50/1.05      ( sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))) != sK2(u1_struct_0(sK8))
% 1.50/1.05      | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != u1_struct_0(sK8)
% 1.50/1.05      | r2_hidden(sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))),k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9))) = iProver_top
% 1.50/1.05      | r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8)) != iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_2170]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1164,plain,
% 1.50/1.05      ( sK2(X0_54) = sK2(X1_54) | X0_54 != X1_54 ),
% 1.50/1.05      theory(equality) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1669,plain,
% 1.50/1.05      ( sK2(X0_54) = sK2(u1_struct_0(sK8)) | X0_54 != u1_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1164]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_2010,plain,
% 1.50/1.05      ( sK2(k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))) = sK2(u1_struct_0(sK8))
% 1.50/1.05      | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) != u1_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1669]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_24,negated_conjecture,
% 1.50/1.05      ( r1_tsep_1(sK8,sK9) | r1_tsep_1(sK9,sK8) ),
% 1.50/1.05      inference(cnf_transformation,[],[f81]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1153,negated_conjecture,
% 1.50/1.05      ( r1_tsep_1(sK8,sK9) | r1_tsep_1(sK9,sK8) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_24]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1403,plain,
% 1.50/1.05      ( r1_tsep_1(sK8,sK9) = iProver_top
% 1.50/1.05      | r1_tsep_1(sK9,sK8) = iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_23,plain,
% 1.50/1.05      ( ~ r1_tsep_1(X0,X1)
% 1.50/1.05      | r1_tsep_1(X1,X0)
% 1.50/1.05      | ~ l1_struct_0(X0)
% 1.50/1.05      | ~ l1_struct_0(X1) ),
% 1.50/1.05      inference(cnf_transformation,[],[f73]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1154,plain,
% 1.50/1.05      ( ~ r1_tsep_1(X0_55,X1_55)
% 1.50/1.05      | r1_tsep_1(X1_55,X0_55)
% 1.50/1.05      | ~ l1_struct_0(X0_55)
% 1.50/1.05      | ~ l1_struct_0(X1_55) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_23]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1402,plain,
% 1.50/1.05      ( r1_tsep_1(X0_55,X1_55) != iProver_top
% 1.50/1.05      | r1_tsep_1(X1_55,X0_55) = iProver_top
% 1.50/1.05      | l1_struct_0(X0_55) != iProver_top
% 1.50/1.05      | l1_struct_0(X1_55) != iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1815,plain,
% 1.50/1.05      ( r1_tsep_1(sK9,sK8) = iProver_top
% 1.50/1.05      | l1_struct_0(sK8) != iProver_top
% 1.50/1.05      | l1_struct_0(sK9) != iProver_top ),
% 1.50/1.05      inference(superposition,[status(thm)],[c_1403,c_1402]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_33,plain,
% 1.50/1.05      ( l1_pre_topc(sK7) = iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_51,plain,
% 1.50/1.05      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_53,plain,
% 1.50/1.05      ( l1_pre_topc(sK8) != iProver_top
% 1.50/1.05      | l1_struct_0(sK8) = iProver_top ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_51]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_528,plain,
% 1.50/1.05      ( l1_pre_topc(sK8) = iProver_top
% 1.50/1.05      | l1_pre_topc(sK9) != iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_549,plain,
% 1.50/1.05      ( l1_pre_topc(sK7) != iProver_top
% 1.50/1.05      | l1_pre_topc(sK9) = iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1818,plain,
% 1.50/1.05      ( r1_tsep_1(sK9,sK8) = iProver_top ),
% 1.50/1.05      inference(global_propositional_subsumption,
% 1.50/1.05                [status(thm)],
% 1.50/1.05                [c_1815,c_33,c_53,c_528,c_549,c_601]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1823,plain,
% 1.50/1.05      ( r1_tsep_1(sK8,sK9) = iProver_top
% 1.50/1.05      | l1_struct_0(sK8) != iProver_top
% 1.50/1.05      | l1_struct_0(sK9) != iProver_top ),
% 1.50/1.05      inference(superposition,[status(thm)],[c_1818,c_1402]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1163,plain,
% 1.50/1.05      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 1.50/1.05      theory(equality) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1524,plain,
% 1.50/1.05      ( X0_54 != X1_54
% 1.50/1.05      | X0_54 = u1_struct_0(sK8)
% 1.50/1.05      | u1_struct_0(sK8) != X1_54 ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1163]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1563,plain,
% 1.50/1.05      ( X0_54 = u1_struct_0(sK8)
% 1.50/1.05      | X0_54 != k2_struct_0(sK8)
% 1.50/1.05      | u1_struct_0(sK8) != k2_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1524]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1595,plain,
% 1.50/1.05      ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = u1_struct_0(sK8)
% 1.50/1.05      | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) != k2_struct_0(sK8)
% 1.50/1.05      | u1_struct_0(sK8) != k2_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1563]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1594,plain,
% 1.50/1.05      ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = u1_struct_0(sK8)
% 1.50/1.05      | k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) != k2_struct_0(sK8)
% 1.50/1.05      | u1_struct_0(sK8) != k2_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1563]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_3,plain,
% 1.50/1.05      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.50/1.05      inference(cnf_transformation,[],[f53]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_16,plain,
% 1.50/1.05      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 1.50/1.05      inference(cnf_transformation,[],[f57]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_622,plain,
% 1.50/1.05      ( ~ sP0(X0,X1)
% 1.50/1.05      | k3_xboole_0(X2,X3) = X2
% 1.50/1.05      | k2_struct_0(X1) != X3
% 1.50/1.05      | k2_struct_0(X0) != X2 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_623,plain,
% 1.50/1.05      ( ~ sP0(X0,X1)
% 1.50/1.05      | k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_622]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_17,plain,
% 1.50/1.05      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 1.50/1.05      inference(cnf_transformation,[],[f67]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_6,plain,
% 1.50/1.05      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 1.50/1.05      inference(cnf_transformation,[],[f55]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_412,plain,
% 1.50/1.05      ( sP0(X0,X1)
% 1.50/1.05      | ~ m1_pre_topc(X0,X1)
% 1.50/1.05      | ~ l1_pre_topc(X1)
% 1.50/1.05      | ~ l1_pre_topc(X0) ),
% 1.50/1.05      inference(resolution,[status(thm)],[c_17,c_6]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_416,plain,
% 1.50/1.05      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 1.50/1.05      inference(global_propositional_subsumption,
% 1.50/1.05                [status(thm)],
% 1.50/1.05                [c_412,c_19]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_417,plain,
% 1.50/1.05      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 1.50/1.05      inference(renaming,[status(thm)],[c_416]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_28,negated_conjecture,
% 1.50/1.05      ( m1_pre_topc(sK8,sK7) ),
% 1.50/1.05      inference(cnf_transformation,[],[f77]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_562,plain,
% 1.50/1.05      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK7 != X1 | sK8 != X0 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_417,c_28]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_563,plain,
% 1.50/1.05      ( sP0(sK8,sK7) | ~ l1_pre_topc(sK7) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_562]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_565,plain,
% 1.50/1.05      ( sP0(sK8,sK7) ),
% 1.50/1.05      inference(global_propositional_subsumption,
% 1.50/1.05                [status(thm)],
% 1.50/1.05                [c_563,c_30]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_829,plain,
% 1.50/1.05      ( k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
% 1.50/1.05      | sK7 != X1
% 1.50/1.05      | sK8 != X0 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_623,c_565]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_830,plain,
% 1.50/1.05      ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_829]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1144,plain,
% 1.50/1.05      ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) = k2_struct_0(sK8) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_830]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_516,plain,
% 1.50/1.05      ( sP0(X0,X1) | ~ l1_pre_topc(X1) | sK8 != X0 | sK9 != X1 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_417,c_25]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_517,plain,
% 1.50/1.05      ( sP0(sK8,sK9) | ~ l1_pre_topc(sK9) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_516]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_557,plain,
% 1.50/1.05      ( sP0(sK8,sK9) ),
% 1.50/1.05      inference(backward_subsumption_resolution,
% 1.50/1.05                [status(thm)],
% 1.50/1.05                [c_550,c_517]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_819,plain,
% 1.50/1.05      ( k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0)
% 1.50/1.05      | sK8 != X0
% 1.50/1.05      | sK9 != X1 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_623,c_557]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_820,plain,
% 1.50/1.05      ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = k2_struct_0(sK8) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_819]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1146,plain,
% 1.50/1.05      ( k3_xboole_0(k2_struct_0(sK8),k2_struct_0(sK9)) = k2_struct_0(sK8) ),
% 1.50/1.05      inference(subtyping,[status(esa)],[c_820]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_1182,plain,
% 1.50/1.05      ( ~ l1_struct_0(sK8) | u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_1157]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_0,plain,
% 1.50/1.05      ( r2_hidden(sK2(X0),X0) | v1_xboole_0(X0) ),
% 1.50/1.05      inference(cnf_transformation,[],[f50]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_20,plain,
% 1.50/1.05      ( v2_struct_0(X0)
% 1.50/1.05      | ~ l1_struct_0(X0)
% 1.50/1.05      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.50/1.05      inference(cnf_transformation,[],[f70]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_354,plain,
% 1.50/1.05      ( r2_hidden(sK2(X0),X0)
% 1.50/1.05      | v2_struct_0(X1)
% 1.50/1.05      | ~ l1_struct_0(X1)
% 1.50/1.05      | u1_struct_0(X1) != X0 ),
% 1.50/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_355,plain,
% 1.50/1.05      ( r2_hidden(sK2(u1_struct_0(X0)),u1_struct_0(X0))
% 1.50/1.05      | v2_struct_0(X0)
% 1.50/1.05      | ~ l1_struct_0(X0) ),
% 1.50/1.05      inference(unflattening,[status(thm)],[c_354]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_356,plain,
% 1.50/1.05      ( r2_hidden(sK2(u1_struct_0(X0)),u1_struct_0(X0)) = iProver_top
% 1.50/1.05      | v2_struct_0(X0) = iProver_top
% 1.50/1.05      | l1_struct_0(X0) != iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_358,plain,
% 1.50/1.05      ( r2_hidden(sK2(u1_struct_0(sK8)),u1_struct_0(sK8)) = iProver_top
% 1.50/1.05      | v2_struct_0(sK8) = iProver_top
% 1.50/1.05      | l1_struct_0(sK8) != iProver_top ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_356]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_52,plain,
% 1.50/1.05      ( ~ l1_pre_topc(sK8) | l1_struct_0(sK8) ),
% 1.50/1.05      inference(instantiation,[status(thm)],[c_18]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_29,negated_conjecture,
% 1.50/1.05      ( ~ v2_struct_0(sK8) ),
% 1.50/1.05      inference(cnf_transformation,[],[f76]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(c_34,plain,
% 1.50/1.05      ( v2_struct_0(sK8) != iProver_top ),
% 1.50/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.50/1.05  
% 1.50/1.05  cnf(contradiction,plain,
% 1.50/1.05      ( $false ),
% 1.50/1.05      inference(minisat,
% 1.50/1.05                [status(thm)],
% 1.50/1.05                [c_2897,c_2584,c_2175,c_2010,c_1823,c_1595,c_1594,c_1144,
% 1.50/1.05                 c_1146,c_1182,c_601,c_549,c_548,c_528,c_527,c_358,c_53,
% 1.50/1.05                 c_52,c_34,c_33,c_30]) ).
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.50/1.05  
% 1.50/1.05  ------                               Statistics
% 1.50/1.05  
% 1.50/1.05  ------ General
% 1.50/1.05  
% 1.50/1.05  abstr_ref_over_cycles:                  0
% 1.50/1.05  abstr_ref_under_cycles:                 0
% 1.50/1.05  gc_basic_clause_elim:                   0
% 1.50/1.05  forced_gc_time:                         0
% 1.50/1.05  parsing_time:                           0.007
% 1.50/1.05  unif_index_cands_time:                  0.
% 1.50/1.05  unif_index_add_time:                    0.
% 1.50/1.05  orderings_time:                         0.
% 1.50/1.05  out_proof_time:                         0.01
% 1.50/1.05  total_time:                             0.083
% 1.50/1.05  num_of_symbols:                         63
% 1.50/1.05  num_of_terms:                           1778
% 1.50/1.05  
% 1.50/1.05  ------ Preprocessing
% 1.50/1.05  
% 1.50/1.05  num_of_splits:                          0
% 1.50/1.05  num_of_split_atoms:                     0
% 1.50/1.05  num_of_reused_defs:                     0
% 1.50/1.05  num_eq_ax_congr_red:                    38
% 1.50/1.05  num_of_sem_filtered_clauses:            6
% 1.50/1.05  num_of_subtypes:                        3
% 1.50/1.05  monotx_restored_types:                  0
% 1.50/1.05  sat_num_of_epr_types:                   0
% 1.50/1.05  sat_num_of_non_cyclic_types:            0
% 1.50/1.05  sat_guarded_non_collapsed_types:        0
% 1.50/1.05  num_pure_diseq_elim:                    0
% 1.50/1.05  simp_replaced_by:                       0
% 1.50/1.05  res_preprocessed:                       117
% 1.50/1.05  prep_upred:                             0
% 1.50/1.05  prep_unflattend:                        47
% 1.50/1.05  smt_new_axioms:                         0
% 1.50/1.05  pred_elim_cands:                        4
% 1.50/1.05  pred_elim:                              7
% 1.50/1.05  pred_elim_cl:                           11
% 1.50/1.05  pred_elim_cycles:                       13
% 1.50/1.05  merged_defs:                            0
% 1.50/1.05  merged_defs_ncl:                        0
% 1.50/1.05  bin_hyper_res:                          0
% 1.50/1.05  prep_cycles:                            5
% 1.50/1.05  pred_elim_time:                         0.006
% 1.50/1.05  splitting_time:                         0.
% 1.50/1.05  sem_filter_time:                        0.
% 1.50/1.05  monotx_time:                            0.
% 1.50/1.05  subtype_inf_time:                       0.
% 1.50/1.05  
% 1.50/1.05  ------ Problem properties
% 1.50/1.05  
% 1.50/1.05  clauses:                                16
% 1.50/1.05  conjectures:                            1
% 1.50/1.05  epr:                                    5
% 1.50/1.05  horn:                                   14
% 1.50/1.05  ground:                                 10
% 1.50/1.05  unary:                                  9
% 1.50/1.05  binary:                                 4
% 1.50/1.05  lits:                                   29
% 1.50/1.05  lits_eq:                                4
% 1.50/1.05  fd_pure:                                0
% 1.50/1.05  fd_pseudo:                              0
% 1.50/1.05  fd_cond:                                0
% 1.50/1.05  fd_pseudo_cond:                         0
% 1.50/1.05  ac_symbols:                             0
% 1.50/1.05  
% 1.50/1.05  ------ Propositional Solver
% 1.50/1.05  
% 1.50/1.05  prop_solver_calls:                      34
% 1.50/1.05  prop_fast_solver_calls:                 746
% 1.50/1.05  smt_solver_calls:                       0
% 1.50/1.05  smt_fast_solver_calls:                  0
% 1.50/1.05  prop_num_of_clauses:                    807
% 1.50/1.05  prop_preprocess_simplified:             3319
% 1.50/1.05  prop_fo_subsumed:                       17
% 1.50/1.05  prop_solver_time:                       0.
% 1.50/1.05  smt_solver_time:                        0.
% 1.50/1.05  smt_fast_solver_time:                   0.
% 1.50/1.05  prop_fast_solver_time:                  0.
% 1.50/1.05  prop_unsat_core_time:                   0.
% 1.50/1.05  
% 1.50/1.05  ------ QBF
% 1.50/1.05  
% 1.50/1.05  qbf_q_res:                              0
% 1.50/1.05  qbf_num_tautologies:                    0
% 1.50/1.05  qbf_prep_cycles:                        0
% 1.50/1.05  
% 1.50/1.05  ------ BMC1
% 1.50/1.05  
% 1.50/1.05  bmc1_current_bound:                     -1
% 1.50/1.05  bmc1_last_solved_bound:                 -1
% 1.50/1.05  bmc1_unsat_core_size:                   -1
% 1.50/1.05  bmc1_unsat_core_parents_size:           -1
% 1.50/1.05  bmc1_merge_next_fun:                    0
% 1.50/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.50/1.05  
% 1.50/1.05  ------ Instantiation
% 1.50/1.05  
% 1.50/1.05  inst_num_of_clauses:                    230
% 1.50/1.05  inst_num_in_passive:                    43
% 1.50/1.05  inst_num_in_active:                     171
% 1.50/1.05  inst_num_in_unprocessed:                16
% 1.50/1.05  inst_num_of_loops:                      190
% 1.50/1.05  inst_num_of_learning_restarts:          0
% 1.50/1.05  inst_num_moves_active_passive:          12
% 1.50/1.05  inst_lit_activity:                      0
% 1.50/1.05  inst_lit_activity_moves:                0
% 1.50/1.05  inst_num_tautologies:                   0
% 1.50/1.05  inst_num_prop_implied:                  0
% 1.50/1.05  inst_num_existing_simplified:           0
% 1.50/1.05  inst_num_eq_res_simplified:             0
% 1.50/1.05  inst_num_child_elim:                    0
% 1.50/1.05  inst_num_of_dismatching_blockings:      36
% 1.50/1.05  inst_num_of_non_proper_insts:           254
% 1.50/1.05  inst_num_of_duplicates:                 0
% 1.50/1.05  inst_inst_num_from_inst_to_res:         0
% 1.50/1.05  inst_dismatching_checking_time:         0.
% 1.50/1.05  
% 1.50/1.05  ------ Resolution
% 1.50/1.05  
% 1.50/1.05  res_num_of_clauses:                     0
% 1.50/1.05  res_num_in_passive:                     0
% 1.50/1.05  res_num_in_active:                      0
% 1.50/1.05  res_num_of_loops:                       122
% 1.50/1.05  res_forward_subset_subsumed:            87
% 1.50/1.05  res_backward_subset_subsumed:           0
% 1.50/1.05  res_forward_subsumed:                   0
% 1.50/1.05  res_backward_subsumed:                  0
% 1.50/1.05  res_forward_subsumption_resolution:     0
% 1.50/1.05  res_backward_subsumption_resolution:    5
% 1.50/1.05  res_clause_to_clause_subsumption:       82
% 1.50/1.05  res_orphan_elimination:                 0
% 1.50/1.05  res_tautology_del:                      50
% 1.50/1.05  res_num_eq_res_simplified:              0
% 1.50/1.05  res_num_sel_changes:                    0
% 1.50/1.05  res_moves_from_active_to_pass:          0
% 1.50/1.05  
% 1.50/1.05  ------ Superposition
% 1.50/1.05  
% 1.50/1.05  sup_time_total:                         0.
% 1.50/1.05  sup_time_generating:                    0.
% 1.50/1.05  sup_time_sim_full:                      0.
% 1.50/1.05  sup_time_sim_immed:                     0.
% 1.50/1.05  
% 1.50/1.05  sup_num_of_clauses:                     55
% 1.50/1.05  sup_num_in_active:                      34
% 1.50/1.05  sup_num_in_passive:                     21
% 1.50/1.05  sup_num_of_loops:                       37
% 1.50/1.05  sup_fw_superposition:                   28
% 1.50/1.05  sup_bw_superposition:                   23
% 1.50/1.05  sup_immediate_simplified:               1
% 1.50/1.05  sup_given_eliminated:                   0
% 1.50/1.05  comparisons_done:                       0
% 1.50/1.05  comparisons_avoided:                    0
% 1.50/1.05  
% 1.50/1.05  ------ Simplifications
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  sim_fw_subset_subsumed:                 1
% 1.50/1.05  sim_bw_subset_subsumed:                 1
% 1.50/1.05  sim_fw_subsumed:                        0
% 1.50/1.05  sim_bw_subsumed:                        0
% 1.50/1.05  sim_fw_subsumption_res:                 0
% 1.50/1.05  sim_bw_subsumption_res:                 0
% 1.50/1.05  sim_tautology_del:                      5
% 1.50/1.05  sim_eq_tautology_del:                   0
% 1.50/1.05  sim_eq_res_simp:                        0
% 1.50/1.05  sim_fw_demodulated:                     0
% 1.50/1.05  sim_bw_demodulated:                     3
% 1.50/1.05  sim_light_normalised:                   0
% 1.50/1.05  sim_joinable_taut:                      0
% 1.50/1.05  sim_joinable_simp:                      0
% 1.50/1.05  sim_ac_normalised:                      0
% 1.50/1.05  sim_smt_subsumption:                    0
% 1.50/1.05  
%------------------------------------------------------------------------------
