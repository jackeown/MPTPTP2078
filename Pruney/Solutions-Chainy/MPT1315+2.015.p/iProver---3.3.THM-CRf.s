%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:46 EST 2020

% Result     : Theorem 10.10s
% Output     : CNFRefutation 10.10s
% Verified   : 
% Statistics : Number of formulae       :  146 (1071 expanded)
%              Number of clauses        :   73 ( 287 expanded)
%              Number of leaves         :   23 ( 347 expanded)
%              Depth                    :   19
%              Number of atoms          :  552 (5867 expanded)
%              Number of equality atoms :  179 (1120 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v4_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v4_pre_topc(sK9,X2)
        & sK9 = X1
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v4_pre_topc(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v4_pre_topc(X3,sK8)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) )
        & v4_pre_topc(X1,X0)
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(X3,X2)
                & sK7 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v4_pre_topc(sK7,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v4_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,sK6)
              & m1_pre_topc(X2,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ~ v4_pre_topc(sK9,sK8)
    & sK7 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v4_pre_topc(sK7,sK6)
    & m1_pre_topc(sK8,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f29,f48,f47,f46,f45])).

fof(f82,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f31,f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f54])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK5(X0,X1,X2),X0)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f84,plain,(
    ~ v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    v4_pre_topc(sK9,sK6) ),
    inference(definition_unfolding,[],[f81,f83])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(definition_unfolding,[],[f79,f83])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2113,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_18,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2122,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2758,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_2122])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_37,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_750,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_751,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_752,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_2280,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2281,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2280])).

cnf(c_3099,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2758,c_33,c_37,c_752,c_2281])).

cnf(c_17,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_370,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_17,c_6])).

cnf(c_374,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_20])).

cnf(c_375,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_418,plain,
    ( ~ sP0(X0,X1)
    | k2_struct_0(X1) != X2
    | k2_struct_0(X0) != X3
    | k1_setfam_1(k2_tarski(X3,X2)) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_419,plain,
    ( ~ sP0(X0,X1)
    | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1087,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_375,c_419])).

cnf(c_2107,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_3105,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9))
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_2107])).

cnf(c_2355,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_5841,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3105,c_32,c_28,c_751,c_2280,c_2355])).

cnf(c_2121,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3104,plain,
    ( l1_pre_topc(k1_pre_topc(sK8,sK9)) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_2121])).

cnf(c_4410,plain,
    ( l1_pre_topc(k1_pre_topc(sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3104,c_33,c_752])).

cnf(c_19,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_356,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_19,c_4])).

cnf(c_2108,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_4415,plain,
    ( u1_struct_0(k1_pre_topc(sK8,sK9)) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
    inference(superposition,[status(thm)],[c_4410,c_2108])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2120,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2631,plain,
    ( u1_struct_0(k1_pre_topc(sK8,sK9)) = sK9
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2113,c_2120])).

cnf(c_2288,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8)
    | u1_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2963,plain,
    ( u1_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2631,c_32,c_28,c_751,c_2288])).

cnf(c_4416,plain,
    ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_4415,c_2963])).

cnf(c_5843,plain,
    ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_5841,c_4416])).

cnf(c_2111,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2499,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2111,c_2121])).

cnf(c_2779,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2499,c_33,c_752])).

cnf(c_3200,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_2779,c_2108])).

cnf(c_23,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2118,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4181,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3200,c_2118])).

cnf(c_4230,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4181,c_3200])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2124,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2124,c_1])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2123,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2617,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2139,c_2123])).

cnf(c_25367,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4230,c_2617])).

cnf(c_25377,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))),sK8) = iProver_top
    | v4_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5843,c_25367])).

cnf(c_25378,plain,
    ( v4_pre_topc(sK9,X0) != iProver_top
    | v4_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25377,c_5843])).

cnf(c_25380,plain,
    ( v4_pre_topc(sK9,sK6) != iProver_top
    | v4_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25378])).

cnf(c_4067,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3200,c_2113])).

cnf(c_27,negated_conjecture,
    ( ~ v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v4_pre_topc(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,negated_conjecture,
    ( v4_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( v4_pre_topc(sK9,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_35,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25380,c_4067,c_38,c_36,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:12:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 10.10/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.10/2.00  
% 10.10/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.10/2.00  
% 10.10/2.00  ------  iProver source info
% 10.10/2.00  
% 10.10/2.00  git: date: 2020-06-30 10:37:57 +0100
% 10.10/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.10/2.00  git: non_committed_changes: false
% 10.10/2.00  git: last_make_outside_of_git: false
% 10.10/2.00  
% 10.10/2.00  ------ 
% 10.10/2.00  
% 10.10/2.00  ------ Input Options
% 10.10/2.00  
% 10.10/2.00  --out_options                           all
% 10.10/2.00  --tptp_safe_out                         true
% 10.10/2.00  --problem_path                          ""
% 10.10/2.00  --include_path                          ""
% 10.10/2.00  --clausifier                            res/vclausify_rel
% 10.10/2.00  --clausifier_options                    --mode clausify
% 10.10/2.00  --stdin                                 false
% 10.10/2.00  --stats_out                             all
% 10.10/2.00  
% 10.10/2.00  ------ General Options
% 10.10/2.00  
% 10.10/2.00  --fof                                   false
% 10.10/2.00  --time_out_real                         305.
% 10.10/2.00  --time_out_virtual                      -1.
% 10.10/2.00  --symbol_type_check                     false
% 10.10/2.00  --clausify_out                          false
% 10.10/2.00  --sig_cnt_out                           false
% 10.10/2.00  --trig_cnt_out                          false
% 10.10/2.00  --trig_cnt_out_tolerance                1.
% 10.10/2.00  --trig_cnt_out_sk_spl                   false
% 10.10/2.00  --abstr_cl_out                          false
% 10.10/2.00  
% 10.10/2.00  ------ Global Options
% 10.10/2.00  
% 10.10/2.00  --schedule                              default
% 10.10/2.00  --add_important_lit                     false
% 10.10/2.00  --prop_solver_per_cl                    1000
% 10.10/2.00  --min_unsat_core                        false
% 10.10/2.00  --soft_assumptions                      false
% 10.10/2.00  --soft_lemma_size                       3
% 10.10/2.00  --prop_impl_unit_size                   0
% 10.10/2.00  --prop_impl_unit                        []
% 10.10/2.00  --share_sel_clauses                     true
% 10.10/2.00  --reset_solvers                         false
% 10.10/2.00  --bc_imp_inh                            [conj_cone]
% 10.10/2.00  --conj_cone_tolerance                   3.
% 10.10/2.00  --extra_neg_conj                        none
% 10.10/2.00  --large_theory_mode                     true
% 10.10/2.00  --prolific_symb_bound                   200
% 10.10/2.00  --lt_threshold                          2000
% 10.10/2.00  --clause_weak_htbl                      true
% 10.10/2.00  --gc_record_bc_elim                     false
% 10.10/2.00  
% 10.10/2.00  ------ Preprocessing Options
% 10.10/2.00  
% 10.10/2.00  --preprocessing_flag                    true
% 10.10/2.00  --time_out_prep_mult                    0.1
% 10.10/2.00  --splitting_mode                        input
% 10.10/2.00  --splitting_grd                         true
% 10.10/2.00  --splitting_cvd                         false
% 10.10/2.00  --splitting_cvd_svl                     false
% 10.10/2.00  --splitting_nvd                         32
% 10.10/2.00  --sub_typing                            true
% 10.10/2.00  --prep_gs_sim                           true
% 10.10/2.00  --prep_unflatten                        true
% 10.10/2.00  --prep_res_sim                          true
% 10.10/2.00  --prep_upred                            true
% 10.10/2.00  --prep_sem_filter                       exhaustive
% 10.10/2.00  --prep_sem_filter_out                   false
% 10.10/2.00  --pred_elim                             true
% 10.10/2.00  --res_sim_input                         true
% 10.10/2.00  --eq_ax_congr_red                       true
% 10.10/2.00  --pure_diseq_elim                       true
% 10.10/2.00  --brand_transform                       false
% 10.10/2.00  --non_eq_to_eq                          false
% 10.10/2.00  --prep_def_merge                        true
% 10.10/2.00  --prep_def_merge_prop_impl              false
% 10.10/2.00  --prep_def_merge_mbd                    true
% 10.10/2.00  --prep_def_merge_tr_red                 false
% 10.10/2.00  --prep_def_merge_tr_cl                  false
% 10.10/2.00  --smt_preprocessing                     true
% 10.10/2.00  --smt_ac_axioms                         fast
% 10.10/2.00  --preprocessed_out                      false
% 10.10/2.00  --preprocessed_stats                    false
% 10.10/2.00  
% 10.10/2.00  ------ Abstraction refinement Options
% 10.10/2.00  
% 10.10/2.00  --abstr_ref                             []
% 10.10/2.00  --abstr_ref_prep                        false
% 10.10/2.00  --abstr_ref_until_sat                   false
% 10.10/2.00  --abstr_ref_sig_restrict                funpre
% 10.10/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 10.10/2.00  --abstr_ref_under                       []
% 10.10/2.00  
% 10.10/2.00  ------ SAT Options
% 10.10/2.00  
% 10.10/2.00  --sat_mode                              false
% 10.10/2.00  --sat_fm_restart_options                ""
% 10.10/2.00  --sat_gr_def                            false
% 10.10/2.00  --sat_epr_types                         true
% 10.10/2.00  --sat_non_cyclic_types                  false
% 10.10/2.00  --sat_finite_models                     false
% 10.10/2.00  --sat_fm_lemmas                         false
% 10.10/2.00  --sat_fm_prep                           false
% 10.10/2.00  --sat_fm_uc_incr                        true
% 10.10/2.00  --sat_out_model                         small
% 10.10/2.00  --sat_out_clauses                       false
% 10.10/2.00  
% 10.10/2.00  ------ QBF Options
% 10.10/2.00  
% 10.10/2.00  --qbf_mode                              false
% 10.10/2.00  --qbf_elim_univ                         false
% 10.10/2.00  --qbf_dom_inst                          none
% 10.10/2.00  --qbf_dom_pre_inst                      false
% 10.10/2.00  --qbf_sk_in                             false
% 10.10/2.00  --qbf_pred_elim                         true
% 10.10/2.00  --qbf_split                             512
% 10.10/2.00  
% 10.10/2.00  ------ BMC1 Options
% 10.10/2.00  
% 10.10/2.00  --bmc1_incremental                      false
% 10.10/2.00  --bmc1_axioms                           reachable_all
% 10.10/2.00  --bmc1_min_bound                        0
% 10.10/2.00  --bmc1_max_bound                        -1
% 10.10/2.00  --bmc1_max_bound_default                -1
% 10.10/2.00  --bmc1_symbol_reachability              true
% 10.10/2.00  --bmc1_property_lemmas                  false
% 10.10/2.00  --bmc1_k_induction                      false
% 10.10/2.00  --bmc1_non_equiv_states                 false
% 10.10/2.00  --bmc1_deadlock                         false
% 10.10/2.00  --bmc1_ucm                              false
% 10.10/2.00  --bmc1_add_unsat_core                   none
% 10.10/2.00  --bmc1_unsat_core_children              false
% 10.10/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 10.10/2.00  --bmc1_out_stat                         full
% 10.10/2.00  --bmc1_ground_init                      false
% 10.10/2.00  --bmc1_pre_inst_next_state              false
% 10.10/2.00  --bmc1_pre_inst_state                   false
% 10.10/2.00  --bmc1_pre_inst_reach_state             false
% 10.10/2.00  --bmc1_out_unsat_core                   false
% 10.10/2.00  --bmc1_aig_witness_out                  false
% 10.10/2.00  --bmc1_verbose                          false
% 10.10/2.00  --bmc1_dump_clauses_tptp                false
% 10.10/2.00  --bmc1_dump_unsat_core_tptp             false
% 10.10/2.00  --bmc1_dump_file                        -
% 10.10/2.00  --bmc1_ucm_expand_uc_limit              128
% 10.10/2.00  --bmc1_ucm_n_expand_iterations          6
% 10.10/2.00  --bmc1_ucm_extend_mode                  1
% 10.10/2.00  --bmc1_ucm_init_mode                    2
% 10.10/2.00  --bmc1_ucm_cone_mode                    none
% 10.10/2.00  --bmc1_ucm_reduced_relation_type        0
% 10.10/2.00  --bmc1_ucm_relax_model                  4
% 10.10/2.00  --bmc1_ucm_full_tr_after_sat            true
% 10.10/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 10.10/2.00  --bmc1_ucm_layered_model                none
% 10.10/2.00  --bmc1_ucm_max_lemma_size               10
% 10.10/2.00  
% 10.10/2.00  ------ AIG Options
% 10.10/2.00  
% 10.10/2.00  --aig_mode                              false
% 10.10/2.00  
% 10.10/2.00  ------ Instantiation Options
% 10.10/2.00  
% 10.10/2.00  --instantiation_flag                    true
% 10.10/2.00  --inst_sos_flag                         false
% 10.10/2.00  --inst_sos_phase                        true
% 10.10/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.10/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.10/2.00  --inst_lit_sel_side                     num_symb
% 10.10/2.00  --inst_solver_per_active                1400
% 10.10/2.00  --inst_solver_calls_frac                1.
% 10.10/2.00  --inst_passive_queue_type               priority_queues
% 10.10/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.10/2.00  --inst_passive_queues_freq              [25;2]
% 10.10/2.00  --inst_dismatching                      true
% 10.10/2.00  --inst_eager_unprocessed_to_passive     true
% 10.10/2.00  --inst_prop_sim_given                   true
% 10.10/2.00  --inst_prop_sim_new                     false
% 10.10/2.00  --inst_subs_new                         false
% 10.10/2.00  --inst_eq_res_simp                      false
% 10.10/2.00  --inst_subs_given                       false
% 10.10/2.00  --inst_orphan_elimination               true
% 10.10/2.00  --inst_learning_loop_flag               true
% 10.10/2.00  --inst_learning_start                   3000
% 10.10/2.00  --inst_learning_factor                  2
% 10.10/2.00  --inst_start_prop_sim_after_learn       3
% 10.10/2.00  --inst_sel_renew                        solver
% 10.10/2.00  --inst_lit_activity_flag                true
% 10.10/2.00  --inst_restr_to_given                   false
% 10.10/2.00  --inst_activity_threshold               500
% 10.10/2.00  --inst_out_proof                        true
% 10.10/2.00  
% 10.10/2.00  ------ Resolution Options
% 10.10/2.00  
% 10.10/2.00  --resolution_flag                       true
% 10.10/2.00  --res_lit_sel                           adaptive
% 10.10/2.00  --res_lit_sel_side                      none
% 10.10/2.00  --res_ordering                          kbo
% 10.10/2.00  --res_to_prop_solver                    active
% 10.10/2.00  --res_prop_simpl_new                    false
% 10.10/2.00  --res_prop_simpl_given                  true
% 10.10/2.00  --res_passive_queue_type                priority_queues
% 10.10/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.10/2.00  --res_passive_queues_freq               [15;5]
% 10.10/2.00  --res_forward_subs                      full
% 10.10/2.00  --res_backward_subs                     full
% 10.10/2.00  --res_forward_subs_resolution           true
% 10.10/2.00  --res_backward_subs_resolution          true
% 10.10/2.00  --res_orphan_elimination                true
% 10.10/2.00  --res_time_limit                        2.
% 10.10/2.00  --res_out_proof                         true
% 10.10/2.00  
% 10.10/2.00  ------ Superposition Options
% 10.10/2.00  
% 10.10/2.00  --superposition_flag                    true
% 10.10/2.00  --sup_passive_queue_type                priority_queues
% 10.10/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.10/2.00  --sup_passive_queues_freq               [8;1;4]
% 10.10/2.00  --demod_completeness_check              fast
% 10.10/2.00  --demod_use_ground                      true
% 10.10/2.00  --sup_to_prop_solver                    passive
% 10.10/2.00  --sup_prop_simpl_new                    true
% 10.10/2.00  --sup_prop_simpl_given                  true
% 10.10/2.00  --sup_fun_splitting                     false
% 10.10/2.00  --sup_smt_interval                      50000
% 10.10/2.00  
% 10.10/2.00  ------ Superposition Simplification Setup
% 10.10/2.00  
% 10.10/2.00  --sup_indices_passive                   []
% 10.10/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.10/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.10/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.10/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 10.10/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.10/2.00  --sup_full_bw                           [BwDemod]
% 10.10/2.00  --sup_immed_triv                        [TrivRules]
% 10.10/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.10/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.10/2.00  --sup_immed_bw_main                     []
% 10.10/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.10/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 10.10/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.10/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.10/2.00  
% 10.10/2.00  ------ Combination Options
% 10.10/2.00  
% 10.10/2.00  --comb_res_mult                         3
% 10.10/2.00  --comb_sup_mult                         2
% 10.10/2.00  --comb_inst_mult                        10
% 10.10/2.00  
% 10.10/2.00  ------ Debug Options
% 10.10/2.00  
% 10.10/2.00  --dbg_backtrace                         false
% 10.10/2.00  --dbg_dump_prop_clauses                 false
% 10.10/2.00  --dbg_dump_prop_clauses_file            -
% 10.10/2.00  --dbg_out_stat                          false
% 10.10/2.00  ------ Parsing...
% 10.10/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.10/2.00  
% 10.10/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 10.10/2.00  
% 10.10/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.10/2.00  
% 10.10/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.10/2.00  ------ Proving...
% 10.10/2.00  ------ Problem Properties 
% 10.10/2.00  
% 10.10/2.00  
% 10.10/2.00  clauses                                 19
% 10.10/2.00  conjectures                             6
% 10.10/2.00  EPR                                     5
% 10.10/2.00  Horn                                    19
% 10.10/2.00  unary                                   8
% 10.10/2.00  binary                                  2
% 10.10/2.00  lits                                    49
% 10.10/2.00  lits eq                                 6
% 10.10/2.00  fd_pure                                 0
% 10.10/2.00  fd_pseudo                               0
% 10.10/2.00  fd_cond                                 0
% 10.10/2.00  fd_pseudo_cond                          0
% 10.10/2.00  AC symbols                              0
% 10.10/2.00  
% 10.10/2.00  ------ Schedule dynamic 5 is on 
% 10.10/2.00  
% 10.10/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 10.10/2.00  
% 10.10/2.00  
% 10.10/2.00  ------ 
% 10.10/2.00  Current options:
% 10.10/2.00  ------ 
% 10.10/2.00  
% 10.10/2.00  ------ Input Options
% 10.10/2.00  
% 10.10/2.00  --out_options                           all
% 10.10/2.00  --tptp_safe_out                         true
% 10.10/2.00  --problem_path                          ""
% 10.10/2.00  --include_path                          ""
% 10.10/2.00  --clausifier                            res/vclausify_rel
% 10.10/2.00  --clausifier_options                    --mode clausify
% 10.10/2.00  --stdin                                 false
% 10.10/2.00  --stats_out                             all
% 10.10/2.00  
% 10.10/2.00  ------ General Options
% 10.10/2.00  
% 10.10/2.00  --fof                                   false
% 10.10/2.00  --time_out_real                         305.
% 10.10/2.00  --time_out_virtual                      -1.
% 10.10/2.00  --symbol_type_check                     false
% 10.10/2.00  --clausify_out                          false
% 10.10/2.00  --sig_cnt_out                           false
% 10.10/2.00  --trig_cnt_out                          false
% 10.10/2.00  --trig_cnt_out_tolerance                1.
% 10.10/2.00  --trig_cnt_out_sk_spl                   false
% 10.10/2.00  --abstr_cl_out                          false
% 10.10/2.00  
% 10.10/2.00  ------ Global Options
% 10.10/2.00  
% 10.10/2.00  --schedule                              default
% 10.10/2.00  --add_important_lit                     false
% 10.10/2.00  --prop_solver_per_cl                    1000
% 10.10/2.00  --min_unsat_core                        false
% 10.10/2.00  --soft_assumptions                      false
% 10.10/2.00  --soft_lemma_size                       3
% 10.10/2.00  --prop_impl_unit_size                   0
% 10.10/2.00  --prop_impl_unit                        []
% 10.10/2.00  --share_sel_clauses                     true
% 10.10/2.00  --reset_solvers                         false
% 10.10/2.00  --bc_imp_inh                            [conj_cone]
% 10.10/2.00  --conj_cone_tolerance                   3.
% 10.10/2.00  --extra_neg_conj                        none
% 10.10/2.00  --large_theory_mode                     true
% 10.10/2.00  --prolific_symb_bound                   200
% 10.10/2.00  --lt_threshold                          2000
% 10.10/2.00  --clause_weak_htbl                      true
% 10.10/2.00  --gc_record_bc_elim                     false
% 10.10/2.00  
% 10.10/2.00  ------ Preprocessing Options
% 10.10/2.00  
% 10.10/2.00  --preprocessing_flag                    true
% 10.10/2.00  --time_out_prep_mult                    0.1
% 10.10/2.00  --splitting_mode                        input
% 10.10/2.00  --splitting_grd                         true
% 10.10/2.00  --splitting_cvd                         false
% 10.10/2.00  --splitting_cvd_svl                     false
% 10.10/2.00  --splitting_nvd                         32
% 10.10/2.00  --sub_typing                            true
% 10.10/2.00  --prep_gs_sim                           true
% 10.10/2.00  --prep_unflatten                        true
% 10.10/2.00  --prep_res_sim                          true
% 10.10/2.00  --prep_upred                            true
% 10.10/2.00  --prep_sem_filter                       exhaustive
% 10.10/2.00  --prep_sem_filter_out                   false
% 10.10/2.00  --pred_elim                             true
% 10.10/2.00  --res_sim_input                         true
% 10.10/2.00  --eq_ax_congr_red                       true
% 10.10/2.00  --pure_diseq_elim                       true
% 10.10/2.00  --brand_transform                       false
% 10.10/2.00  --non_eq_to_eq                          false
% 10.10/2.00  --prep_def_merge                        true
% 10.10/2.00  --prep_def_merge_prop_impl              false
% 10.10/2.00  --prep_def_merge_mbd                    true
% 10.10/2.00  --prep_def_merge_tr_red                 false
% 10.10/2.00  --prep_def_merge_tr_cl                  false
% 10.10/2.00  --smt_preprocessing                     true
% 10.10/2.00  --smt_ac_axioms                         fast
% 10.10/2.00  --preprocessed_out                      false
% 10.10/2.00  --preprocessed_stats                    false
% 10.10/2.00  
% 10.10/2.00  ------ Abstraction refinement Options
% 10.10/2.00  
% 10.10/2.00  --abstr_ref                             []
% 10.10/2.00  --abstr_ref_prep                        false
% 10.10/2.00  --abstr_ref_until_sat                   false
% 10.10/2.00  --abstr_ref_sig_restrict                funpre
% 10.10/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 10.10/2.00  --abstr_ref_under                       []
% 10.10/2.00  
% 10.10/2.00  ------ SAT Options
% 10.10/2.00  
% 10.10/2.00  --sat_mode                              false
% 10.10/2.00  --sat_fm_restart_options                ""
% 10.10/2.00  --sat_gr_def                            false
% 10.10/2.00  --sat_epr_types                         true
% 10.10/2.00  --sat_non_cyclic_types                  false
% 10.10/2.00  --sat_finite_models                     false
% 10.10/2.00  --sat_fm_lemmas                         false
% 10.10/2.00  --sat_fm_prep                           false
% 10.10/2.00  --sat_fm_uc_incr                        true
% 10.10/2.00  --sat_out_model                         small
% 10.10/2.00  --sat_out_clauses                       false
% 10.10/2.00  
% 10.10/2.00  ------ QBF Options
% 10.10/2.00  
% 10.10/2.00  --qbf_mode                              false
% 10.10/2.00  --qbf_elim_univ                         false
% 10.10/2.00  --qbf_dom_inst                          none
% 10.10/2.00  --qbf_dom_pre_inst                      false
% 10.10/2.00  --qbf_sk_in                             false
% 10.10/2.00  --qbf_pred_elim                         true
% 10.10/2.00  --qbf_split                             512
% 10.10/2.00  
% 10.10/2.00  ------ BMC1 Options
% 10.10/2.00  
% 10.10/2.00  --bmc1_incremental                      false
% 10.10/2.00  --bmc1_axioms                           reachable_all
% 10.10/2.00  --bmc1_min_bound                        0
% 10.10/2.00  --bmc1_max_bound                        -1
% 10.10/2.00  --bmc1_max_bound_default                -1
% 10.10/2.00  --bmc1_symbol_reachability              true
% 10.10/2.00  --bmc1_property_lemmas                  false
% 10.10/2.00  --bmc1_k_induction                      false
% 10.10/2.00  --bmc1_non_equiv_states                 false
% 10.10/2.00  --bmc1_deadlock                         false
% 10.10/2.00  --bmc1_ucm                              false
% 10.10/2.00  --bmc1_add_unsat_core                   none
% 10.10/2.00  --bmc1_unsat_core_children              false
% 10.10/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 10.10/2.00  --bmc1_out_stat                         full
% 10.10/2.00  --bmc1_ground_init                      false
% 10.10/2.00  --bmc1_pre_inst_next_state              false
% 10.10/2.00  --bmc1_pre_inst_state                   false
% 10.10/2.00  --bmc1_pre_inst_reach_state             false
% 10.10/2.00  --bmc1_out_unsat_core                   false
% 10.10/2.00  --bmc1_aig_witness_out                  false
% 10.10/2.00  --bmc1_verbose                          false
% 10.10/2.00  --bmc1_dump_clauses_tptp                false
% 10.10/2.00  --bmc1_dump_unsat_core_tptp             false
% 10.10/2.00  --bmc1_dump_file                        -
% 10.10/2.00  --bmc1_ucm_expand_uc_limit              128
% 10.10/2.00  --bmc1_ucm_n_expand_iterations          6
% 10.10/2.00  --bmc1_ucm_extend_mode                  1
% 10.10/2.00  --bmc1_ucm_init_mode                    2
% 10.10/2.00  --bmc1_ucm_cone_mode                    none
% 10.10/2.00  --bmc1_ucm_reduced_relation_type        0
% 10.10/2.00  --bmc1_ucm_relax_model                  4
% 10.10/2.00  --bmc1_ucm_full_tr_after_sat            true
% 10.10/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 10.10/2.00  --bmc1_ucm_layered_model                none
% 10.10/2.00  --bmc1_ucm_max_lemma_size               10
% 10.10/2.00  
% 10.10/2.00  ------ AIG Options
% 10.10/2.00  
% 10.10/2.00  --aig_mode                              false
% 10.10/2.00  
% 10.10/2.00  ------ Instantiation Options
% 10.10/2.00  
% 10.10/2.00  --instantiation_flag                    true
% 10.10/2.00  --inst_sos_flag                         false
% 10.10/2.00  --inst_sos_phase                        true
% 10.10/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.10/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.10/2.00  --inst_lit_sel_side                     none
% 10.10/2.00  --inst_solver_per_active                1400
% 10.10/2.00  --inst_solver_calls_frac                1.
% 10.10/2.00  --inst_passive_queue_type               priority_queues
% 10.10/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.10/2.00  --inst_passive_queues_freq              [25;2]
% 10.10/2.00  --inst_dismatching                      true
% 10.10/2.00  --inst_eager_unprocessed_to_passive     true
% 10.10/2.00  --inst_prop_sim_given                   true
% 10.10/2.00  --inst_prop_sim_new                     false
% 10.10/2.00  --inst_subs_new                         false
% 10.10/2.00  --inst_eq_res_simp                      false
% 10.10/2.00  --inst_subs_given                       false
% 10.10/2.00  --inst_orphan_elimination               true
% 10.10/2.00  --inst_learning_loop_flag               true
% 10.10/2.00  --inst_learning_start                   3000
% 10.10/2.00  --inst_learning_factor                  2
% 10.10/2.00  --inst_start_prop_sim_after_learn       3
% 10.10/2.00  --inst_sel_renew                        solver
% 10.10/2.00  --inst_lit_activity_flag                true
% 10.10/2.00  --inst_restr_to_given                   false
% 10.10/2.00  --inst_activity_threshold               500
% 10.10/2.00  --inst_out_proof                        true
% 10.10/2.00  
% 10.10/2.00  ------ Resolution Options
% 10.10/2.00  
% 10.10/2.00  --resolution_flag                       false
% 10.10/2.00  --res_lit_sel                           adaptive
% 10.10/2.00  --res_lit_sel_side                      none
% 10.10/2.00  --res_ordering                          kbo
% 10.10/2.00  --res_to_prop_solver                    active
% 10.10/2.00  --res_prop_simpl_new                    false
% 10.10/2.00  --res_prop_simpl_given                  true
% 10.10/2.00  --res_passive_queue_type                priority_queues
% 10.10/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.10/2.00  --res_passive_queues_freq               [15;5]
% 10.10/2.00  --res_forward_subs                      full
% 10.10/2.00  --res_backward_subs                     full
% 10.10/2.00  --res_forward_subs_resolution           true
% 10.10/2.00  --res_backward_subs_resolution          true
% 10.10/2.00  --res_orphan_elimination                true
% 10.10/2.00  --res_time_limit                        2.
% 10.10/2.00  --res_out_proof                         true
% 10.10/2.00  
% 10.10/2.00  ------ Superposition Options
% 10.10/2.00  
% 10.10/2.00  --superposition_flag                    true
% 10.10/2.00  --sup_passive_queue_type                priority_queues
% 10.10/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.10/2.00  --sup_passive_queues_freq               [8;1;4]
% 10.10/2.00  --demod_completeness_check              fast
% 10.10/2.00  --demod_use_ground                      true
% 10.10/2.00  --sup_to_prop_solver                    passive
% 10.10/2.00  --sup_prop_simpl_new                    true
% 10.10/2.00  --sup_prop_simpl_given                  true
% 10.10/2.00  --sup_fun_splitting                     false
% 10.10/2.00  --sup_smt_interval                      50000
% 10.10/2.00  
% 10.10/2.00  ------ Superposition Simplification Setup
% 10.10/2.00  
% 10.10/2.00  --sup_indices_passive                   []
% 10.10/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.10/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.10/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.10/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 10.10/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.10/2.00  --sup_full_bw                           [BwDemod]
% 10.10/2.00  --sup_immed_triv                        [TrivRules]
% 10.10/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.10/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.10/2.00  --sup_immed_bw_main                     []
% 10.10/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.10/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 10.10/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.10/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.10/2.00  
% 10.10/2.00  ------ Combination Options
% 10.10/2.00  
% 10.10/2.00  --comb_res_mult                         3
% 10.10/2.00  --comb_sup_mult                         2
% 10.10/2.00  --comb_inst_mult                        10
% 10.10/2.00  
% 10.10/2.00  ------ Debug Options
% 10.10/2.00  
% 10.10/2.00  --dbg_backtrace                         false
% 10.10/2.00  --dbg_dump_prop_clauses                 false
% 10.10/2.00  --dbg_dump_prop_clauses_file            -
% 10.10/2.00  --dbg_out_stat                          false
% 10.10/2.00  
% 10.10/2.00  
% 10.10/2.00  
% 10.10/2.00  
% 10.10/2.00  ------ Proving...
% 10.10/2.00  
% 10.10/2.00  
% 10.10/2.00  % SZS status Theorem for theBenchmark.p
% 10.10/2.00  
% 10.10/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 10.10/2.00  
% 10.10/2.00  fof(f14,conjecture,(
% 10.10/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f15,negated_conjecture,(
% 10.10/2.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 10.10/2.00    inference(negated_conjecture,[],[f14])).
% 10.10/2.00  
% 10.10/2.00  fof(f28,plain,(
% 10.10/2.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 10.10/2.00    inference(ennf_transformation,[],[f15])).
% 10.10/2.00  
% 10.10/2.00  fof(f29,plain,(
% 10.10/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 10.10/2.00    inference(flattening,[],[f28])).
% 10.10/2.00  
% 10.10/2.00  fof(f48,plain,(
% 10.10/2.00    ( ! [X2,X1] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v4_pre_topc(sK9,X2) & sK9 = X1 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 10.10/2.00    introduced(choice_axiom,[])).
% 10.10/2.00  
% 10.10/2.00  fof(f47,plain,(
% 10.10/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v4_pre_topc(X3,sK8) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) & v4_pre_topc(X1,X0) & m1_pre_topc(sK8,X0))) )),
% 10.10/2.00    introduced(choice_axiom,[])).
% 10.10/2.00  
% 10.10/2.00  fof(f46,plain,(
% 10.10/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK7,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 10.10/2.00    introduced(choice_axiom,[])).
% 10.10/2.00  
% 10.10/2.00  fof(f45,plain,(
% 10.10/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6))),
% 10.10/2.00    introduced(choice_axiom,[])).
% 10.10/2.00  
% 10.10/2.00  fof(f49,plain,(
% 10.10/2.00    (((~v4_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & v4_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6)),
% 10.10/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f29,f48,f47,f46,f45])).
% 10.10/2.00  
% 10.10/2.00  fof(f82,plain,(
% 10.10/2.00    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 10.10/2.00    inference(cnf_transformation,[],[f49])).
% 10.10/2.00  
% 10.10/2.00  fof(f8,axiom,(
% 10.10/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f16,plain,(
% 10.10/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 10.10/2.00    inference(pure_predicate_removal,[],[f8])).
% 10.10/2.00  
% 10.10/2.00  fof(f21,plain,(
% 10.10/2.00    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 10.10/2.00    inference(ennf_transformation,[],[f16])).
% 10.10/2.00  
% 10.10/2.00  fof(f22,plain,(
% 10.10/2.00    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(flattening,[],[f21])).
% 10.10/2.00  
% 10.10/2.00  fof(f69,plain,(
% 10.10/2.00    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f22])).
% 10.10/2.00  
% 10.10/2.00  fof(f78,plain,(
% 10.10/2.00    l1_pre_topc(sK6)),
% 10.10/2.00    inference(cnf_transformation,[],[f49])).
% 10.10/2.00  
% 10.10/2.00  fof(f10,axiom,(
% 10.10/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f24,plain,(
% 10.10/2.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(ennf_transformation,[],[f10])).
% 10.10/2.00  
% 10.10/2.00  fof(f71,plain,(
% 10.10/2.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f24])).
% 10.10/2.00  
% 10.10/2.00  fof(f80,plain,(
% 10.10/2.00    m1_pre_topc(sK8,sK6)),
% 10.10/2.00    inference(cnf_transformation,[],[f49])).
% 10.10/2.00  
% 10.10/2.00  fof(f7,axiom,(
% 10.10/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f20,plain,(
% 10.10/2.00    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(ennf_transformation,[],[f7])).
% 10.10/2.00  
% 10.10/2.00  fof(f31,plain,(
% 10.10/2.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 10.10/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 10.10/2.00  
% 10.10/2.00  fof(f30,plain,(
% 10.10/2.00    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 10.10/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 10.10/2.00  
% 10.10/2.00  fof(f32,plain,(
% 10.10/2.00    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(definition_folding,[],[f20,f31,f30])).
% 10.10/2.00  
% 10.10/2.00  fof(f68,plain,(
% 10.10/2.00    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f32])).
% 10.10/2.00  
% 10.10/2.00  fof(f33,plain,(
% 10.10/2.00    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 10.10/2.00    inference(nnf_transformation,[],[f31])).
% 10.10/2.00  
% 10.10/2.00  fof(f56,plain,(
% 10.10/2.00    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f33])).
% 10.10/2.00  
% 10.10/2.00  fof(f1,axiom,(
% 10.10/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f17,plain,(
% 10.10/2.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 10.10/2.00    inference(ennf_transformation,[],[f1])).
% 10.10/2.00  
% 10.10/2.00  fof(f50,plain,(
% 10.10/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f17])).
% 10.10/2.00  
% 10.10/2.00  fof(f5,axiom,(
% 10.10/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f54,plain,(
% 10.10/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 10.10/2.00    inference(cnf_transformation,[],[f5])).
% 10.10/2.00  
% 10.10/2.00  fof(f85,plain,(
% 10.10/2.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 10.10/2.00    inference(definition_unfolding,[],[f50,f54])).
% 10.10/2.00  
% 10.10/2.00  fof(f34,plain,(
% 10.10/2.00    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 10.10/2.00    inference(nnf_transformation,[],[f30])).
% 10.10/2.00  
% 10.10/2.00  fof(f35,plain,(
% 10.10/2.00    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 10.10/2.00    inference(flattening,[],[f34])).
% 10.10/2.00  
% 10.10/2.00  fof(f36,plain,(
% 10.10/2.00    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 10.10/2.00    inference(rectify,[],[f35])).
% 10.10/2.00  
% 10.10/2.00  fof(f39,plain,(
% 10.10/2.00    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 10.10/2.00    introduced(choice_axiom,[])).
% 10.10/2.00  
% 10.10/2.00  fof(f38,plain,(
% 10.10/2.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 10.10/2.00    introduced(choice_axiom,[])).
% 10.10/2.00  
% 10.10/2.00  fof(f37,plain,(
% 10.10/2.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 10.10/2.00    introduced(choice_axiom,[])).
% 10.10/2.00  
% 10.10/2.00  fof(f40,plain,(
% 10.10/2.00    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 10.10/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f39,f38,f37])).
% 10.10/2.00  
% 10.10/2.00  fof(f58,plain,(
% 10.10/2.00    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f40])).
% 10.10/2.00  
% 10.10/2.00  fof(f9,axiom,(
% 10.10/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f23,plain,(
% 10.10/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(ennf_transformation,[],[f9])).
% 10.10/2.00  
% 10.10/2.00  fof(f70,plain,(
% 10.10/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f23])).
% 10.10/2.00  
% 10.10/2.00  fof(f6,axiom,(
% 10.10/2.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f19,plain,(
% 10.10/2.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 10.10/2.00    inference(ennf_transformation,[],[f6])).
% 10.10/2.00  
% 10.10/2.00  fof(f55,plain,(
% 10.10/2.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f19])).
% 10.10/2.00  
% 10.10/2.00  fof(f11,axiom,(
% 10.10/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f25,plain,(
% 10.10/2.00    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(ennf_transformation,[],[f11])).
% 10.10/2.00  
% 10.10/2.00  fof(f72,plain,(
% 10.10/2.00    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f25])).
% 10.10/2.00  
% 10.10/2.00  fof(f13,axiom,(
% 10.10/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f27,plain,(
% 10.10/2.00    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(ennf_transformation,[],[f13])).
% 10.10/2.00  
% 10.10/2.00  fof(f41,plain,(
% 10.10/2.00    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(nnf_transformation,[],[f27])).
% 10.10/2.00  
% 10.10/2.00  fof(f42,plain,(
% 10.10/2.00    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(rectify,[],[f41])).
% 10.10/2.00  
% 10.10/2.00  fof(f43,plain,(
% 10.10/2.00    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 10.10/2.00    introduced(choice_axiom,[])).
% 10.10/2.00  
% 10.10/2.00  fof(f44,plain,(
% 10.10/2.00    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 10.10/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 10.10/2.00  
% 10.10/2.00  fof(f77,plain,(
% 10.10/2.00    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 10.10/2.00    inference(cnf_transformation,[],[f44])).
% 10.10/2.00  
% 10.10/2.00  fof(f90,plain,(
% 10.10/2.00    ( ! [X0,X3,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 10.10/2.00    inference(equality_resolution,[],[f77])).
% 10.10/2.00  
% 10.10/2.00  fof(f3,axiom,(
% 10.10/2.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f52,plain,(
% 10.10/2.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 10.10/2.00    inference(cnf_transformation,[],[f3])).
% 10.10/2.00  
% 10.10/2.00  fof(f2,axiom,(
% 10.10/2.00    ! [X0] : k2_subset_1(X0) = X0),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f51,plain,(
% 10.10/2.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 10.10/2.00    inference(cnf_transformation,[],[f2])).
% 10.10/2.00  
% 10.10/2.00  fof(f4,axiom,(
% 10.10/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 10.10/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.10/2.00  
% 10.10/2.00  fof(f18,plain,(
% 10.10/2.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 10.10/2.00    inference(ennf_transformation,[],[f4])).
% 10.10/2.00  
% 10.10/2.00  fof(f53,plain,(
% 10.10/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 10.10/2.00    inference(cnf_transformation,[],[f18])).
% 10.10/2.00  
% 10.10/2.00  fof(f86,plain,(
% 10.10/2.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 10.10/2.00    inference(definition_unfolding,[],[f53,f54])).
% 10.10/2.00  
% 10.10/2.00  fof(f84,plain,(
% 10.10/2.00    ~v4_pre_topc(sK9,sK8)),
% 10.10/2.00    inference(cnf_transformation,[],[f49])).
% 10.10/2.00  
% 10.10/2.00  fof(f81,plain,(
% 10.10/2.00    v4_pre_topc(sK7,sK6)),
% 10.10/2.00    inference(cnf_transformation,[],[f49])).
% 10.10/2.00  
% 10.10/2.00  fof(f83,plain,(
% 10.10/2.00    sK7 = sK9),
% 10.10/2.00    inference(cnf_transformation,[],[f49])).
% 10.10/2.00  
% 10.10/2.00  fof(f87,plain,(
% 10.10/2.00    v4_pre_topc(sK9,sK6)),
% 10.10/2.00    inference(definition_unfolding,[],[f81,f83])).
% 10.10/2.00  
% 10.10/2.00  fof(f79,plain,(
% 10.10/2.00    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 10.10/2.00    inference(cnf_transformation,[],[f49])).
% 10.10/2.00  
% 10.10/2.00  fof(f88,plain,(
% 10.10/2.00    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))),
% 10.10/2.00    inference(definition_unfolding,[],[f79,f83])).
% 10.10/2.00  
% 10.10/2.00  cnf(c_28,negated_conjecture,
% 10.10/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 10.10/2.00      inference(cnf_transformation,[],[f82]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2113,plain,
% 10.10/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_18,plain,
% 10.10/2.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 10.10/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 10.10/2.00      | ~ l1_pre_topc(X0) ),
% 10.10/2.00      inference(cnf_transformation,[],[f69]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2122,plain,
% 10.10/2.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 10.10/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 10.10/2.00      | l1_pre_topc(X0) != iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2758,plain,
% 10.10/2.00      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 10.10/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_2113,c_2122]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_32,negated_conjecture,
% 10.10/2.00      ( l1_pre_topc(sK6) ),
% 10.10/2.00      inference(cnf_transformation,[],[f78]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_33,plain,
% 10.10/2.00      ( l1_pre_topc(sK6) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_37,plain,
% 10.10/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_20,plain,
% 10.10/2.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 10.10/2.00      inference(cnf_transformation,[],[f71]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_30,negated_conjecture,
% 10.10/2.00      ( m1_pre_topc(sK8,sK6) ),
% 10.10/2.00      inference(cnf_transformation,[],[f80]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_750,plain,
% 10.10/2.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X0 | sK8 != X1 ),
% 10.10/2.00      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_751,plain,
% 10.10/2.00      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 10.10/2.00      inference(unflattening,[status(thm)],[c_750]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_752,plain,
% 10.10/2.00      ( l1_pre_topc(sK6) != iProver_top
% 10.10/2.00      | l1_pre_topc(sK8) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2280,plain,
% 10.10/2.00      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
% 10.10/2.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 10.10/2.00      | ~ l1_pre_topc(sK8) ),
% 10.10/2.00      inference(instantiation,[status(thm)],[c_18]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2281,plain,
% 10.10/2.00      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 10.10/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 10.10/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_2280]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_3099,plain,
% 10.10/2.00      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
% 10.10/2.00      inference(global_propositional_subsumption,
% 10.10/2.00                [status(thm)],
% 10.10/2.00                [c_2758,c_33,c_37,c_752,c_2281]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_17,plain,
% 10.10/2.00      ( sP1(X0,X1) | ~ l1_pre_topc(X1) | ~ l1_pre_topc(X0) ),
% 10.10/2.00      inference(cnf_transformation,[],[f68]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_6,plain,
% 10.10/2.00      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 10.10/2.00      inference(cnf_transformation,[],[f56]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_370,plain,
% 10.10/2.00      ( sP0(X0,X1)
% 10.10/2.00      | ~ m1_pre_topc(X0,X1)
% 10.10/2.00      | ~ l1_pre_topc(X1)
% 10.10/2.00      | ~ l1_pre_topc(X0) ),
% 10.10/2.00      inference(resolution,[status(thm)],[c_17,c_6]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_374,plain,
% 10.10/2.00      ( ~ l1_pre_topc(X1) | ~ m1_pre_topc(X0,X1) | sP0(X0,X1) ),
% 10.10/2.00      inference(global_propositional_subsumption,
% 10.10/2.00                [status(thm)],
% 10.10/2.00                [c_370,c_20]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_375,plain,
% 10.10/2.00      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 10.10/2.00      inference(renaming,[status(thm)],[c_374]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_0,plain,
% 10.10/2.00      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 10.10/2.00      inference(cnf_transformation,[],[f85]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_16,plain,
% 10.10/2.00      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 10.10/2.00      inference(cnf_transformation,[],[f58]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_418,plain,
% 10.10/2.00      ( ~ sP0(X0,X1)
% 10.10/2.00      | k2_struct_0(X1) != X2
% 10.10/2.00      | k2_struct_0(X0) != X3
% 10.10/2.00      | k1_setfam_1(k2_tarski(X3,X2)) = X3 ),
% 10.10/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_419,plain,
% 10.10/2.00      ( ~ sP0(X0,X1)
% 10.10/2.00      | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
% 10.10/2.00      inference(unflattening,[status(thm)],[c_418]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_1087,plain,
% 10.10/2.00      ( ~ m1_pre_topc(X0,X1)
% 10.10/2.00      | ~ l1_pre_topc(X1)
% 10.10/2.00      | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
% 10.10/2.00      inference(resolution,[status(thm)],[c_375,c_419]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2107,plain,
% 10.10/2.00      ( k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
% 10.10/2.00      | m1_pre_topc(X0,X1) != iProver_top
% 10.10/2.00      | l1_pre_topc(X1) != iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_1087]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_3105,plain,
% 10.10/2.00      ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9))
% 10.10/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_3099,c_2107]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2355,plain,
% 10.10/2.00      ( ~ m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
% 10.10/2.00      | ~ l1_pre_topc(sK8)
% 10.10/2.00      | k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
% 10.10/2.00      inference(instantiation,[status(thm)],[c_1087]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_5841,plain,
% 10.10/2.00      ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
% 10.10/2.00      inference(global_propositional_subsumption,
% 10.10/2.00                [status(thm)],
% 10.10/2.00                [c_3105,c_32,c_28,c_751,c_2280,c_2355]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2121,plain,
% 10.10/2.00      ( m1_pre_topc(X0,X1) != iProver_top
% 10.10/2.00      | l1_pre_topc(X1) != iProver_top
% 10.10/2.00      | l1_pre_topc(X0) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_3104,plain,
% 10.10/2.00      ( l1_pre_topc(k1_pre_topc(sK8,sK9)) = iProver_top
% 10.10/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_3099,c_2121]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_4410,plain,
% 10.10/2.00      ( l1_pre_topc(k1_pre_topc(sK8,sK9)) = iProver_top ),
% 10.10/2.00      inference(global_propositional_subsumption,
% 10.10/2.00                [status(thm)],
% 10.10/2.00                [c_3104,c_33,c_752]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_19,plain,
% 10.10/2.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 10.10/2.00      inference(cnf_transformation,[],[f70]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_4,plain,
% 10.10/2.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 10.10/2.00      inference(cnf_transformation,[],[f55]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_356,plain,
% 10.10/2.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 10.10/2.00      inference(resolution,[status(thm)],[c_19,c_4]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2108,plain,
% 10.10/2.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 10.10/2.00      | l1_pre_topc(X0) != iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_4415,plain,
% 10.10/2.00      ( u1_struct_0(k1_pre_topc(sK8,sK9)) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_4410,c_2108]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_21,plain,
% 10.10/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 10.10/2.00      | ~ l1_pre_topc(X1)
% 10.10/2.00      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 10.10/2.00      inference(cnf_transformation,[],[f72]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2120,plain,
% 10.10/2.00      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 10.10/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 10.10/2.00      | l1_pre_topc(X0) != iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2631,plain,
% 10.10/2.00      ( u1_struct_0(k1_pre_topc(sK8,sK9)) = sK9
% 10.10/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_2113,c_2120]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2288,plain,
% 10.10/2.00      ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 10.10/2.00      | ~ l1_pre_topc(sK8)
% 10.10/2.00      | u1_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
% 10.10/2.00      inference(instantiation,[status(thm)],[c_21]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2963,plain,
% 10.10/2.00      ( u1_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
% 10.10/2.00      inference(global_propositional_subsumption,
% 10.10/2.00                [status(thm)],
% 10.10/2.00                [c_2631,c_32,c_28,c_751,c_2288]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_4416,plain,
% 10.10/2.00      ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
% 10.10/2.00      inference(light_normalisation,[status(thm)],[c_4415,c_2963]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_5843,plain,
% 10.10/2.00      ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
% 10.10/2.00      inference(light_normalisation,[status(thm)],[c_5841,c_4416]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2111,plain,
% 10.10/2.00      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2499,plain,
% 10.10/2.00      ( l1_pre_topc(sK6) != iProver_top
% 10.10/2.00      | l1_pre_topc(sK8) = iProver_top ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_2111,c_2121]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2779,plain,
% 10.10/2.00      ( l1_pre_topc(sK8) = iProver_top ),
% 10.10/2.00      inference(global_propositional_subsumption,
% 10.10/2.00                [status(thm)],
% 10.10/2.00                [c_2499,c_33,c_752]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_3200,plain,
% 10.10/2.00      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_2779,c_2108]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_23,plain,
% 10.10/2.00      ( ~ v4_pre_topc(X0,X1)
% 10.10/2.00      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 10.10/2.00      | ~ m1_pre_topc(X2,X1)
% 10.10/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 10.10/2.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 10.10/2.00      | ~ l1_pre_topc(X1) ),
% 10.10/2.00      inference(cnf_transformation,[],[f90]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2118,plain,
% 10.10/2.00      ( v4_pre_topc(X0,X1) != iProver_top
% 10.10/2.00      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
% 10.10/2.00      | m1_pre_topc(X2,X1) != iProver_top
% 10.10/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 10.10/2.00      | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 10.10/2.00      | l1_pre_topc(X1) != iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_4181,plain,
% 10.10/2.00      ( v4_pre_topc(X0,X1) != iProver_top
% 10.10/2.00      | v4_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
% 10.10/2.00      | m1_pre_topc(sK8,X1) != iProver_top
% 10.10/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 10.10/2.00      | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 10.10/2.00      | l1_pre_topc(X1) != iProver_top ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_3200,c_2118]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_4230,plain,
% 10.10/2.00      ( v4_pre_topc(X0,X1) != iProver_top
% 10.10/2.00      | v4_pre_topc(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
% 10.10/2.00      | m1_pre_topc(sK8,X1) != iProver_top
% 10.10/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 10.10/2.00      | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 10.10/2.00      | l1_pre_topc(X1) != iProver_top ),
% 10.10/2.00      inference(light_normalisation,[status(thm)],[c_4181,c_3200]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2,plain,
% 10.10/2.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 10.10/2.00      inference(cnf_transformation,[],[f52]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2124,plain,
% 10.10/2.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_1,plain,
% 10.10/2.00      ( k2_subset_1(X0) = X0 ),
% 10.10/2.00      inference(cnf_transformation,[],[f51]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2139,plain,
% 10.10/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 10.10/2.00      inference(light_normalisation,[status(thm)],[c_2124,c_1]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_3,plain,
% 10.10/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 10.10/2.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 10.10/2.00      inference(cnf_transformation,[],[f86]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2123,plain,
% 10.10/2.00      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 10.10/2.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_2617,plain,
% 10.10/2.00      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_2139,c_2123]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_25367,plain,
% 10.10/2.00      ( v4_pre_topc(X0,X1) != iProver_top
% 10.10/2.00      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),sK8) = iProver_top
% 10.10/2.00      | m1_pre_topc(sK8,X1) != iProver_top
% 10.10/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 10.10/2.00      | m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 10.10/2.00      | l1_pre_topc(X1) != iProver_top ),
% 10.10/2.00      inference(demodulation,[status(thm)],[c_4230,c_2617]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_25377,plain,
% 10.10/2.00      ( v4_pre_topc(k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))),sK8) = iProver_top
% 10.10/2.00      | v4_pre_topc(sK9,X0) != iProver_top
% 10.10/2.00      | m1_pre_topc(sK8,X0) != iProver_top
% 10.10/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 10.10/2.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 10.10/2.00      | l1_pre_topc(X0) != iProver_top ),
% 10.10/2.00      inference(superposition,[status(thm)],[c_5843,c_25367]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_25378,plain,
% 10.10/2.00      ( v4_pre_topc(sK9,X0) != iProver_top
% 10.10/2.00      | v4_pre_topc(sK9,sK8) = iProver_top
% 10.10/2.00      | m1_pre_topc(sK8,X0) != iProver_top
% 10.10/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 10.10/2.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 10.10/2.00      | l1_pre_topc(X0) != iProver_top ),
% 10.10/2.00      inference(light_normalisation,[status(thm)],[c_25377,c_5843]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_25380,plain,
% 10.10/2.00      ( v4_pre_topc(sK9,sK6) != iProver_top
% 10.10/2.00      | v4_pre_topc(sK9,sK8) = iProver_top
% 10.10/2.00      | m1_pre_topc(sK8,sK6) != iProver_top
% 10.10/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 10.10/2.00      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 10.10/2.00      | l1_pre_topc(sK6) != iProver_top ),
% 10.10/2.00      inference(instantiation,[status(thm)],[c_25378]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_4067,plain,
% 10.10/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
% 10.10/2.00      inference(demodulation,[status(thm)],[c_3200,c_2113]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_27,negated_conjecture,
% 10.10/2.00      ( ~ v4_pre_topc(sK9,sK8) ),
% 10.10/2.00      inference(cnf_transformation,[],[f84]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_38,plain,
% 10.10/2.00      ( v4_pre_topc(sK9,sK8) != iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_29,negated_conjecture,
% 10.10/2.00      ( v4_pre_topc(sK9,sK6) ),
% 10.10/2.00      inference(cnf_transformation,[],[f87]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_36,plain,
% 10.10/2.00      ( v4_pre_topc(sK9,sK6) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_35,plain,
% 10.10/2.00      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_31,negated_conjecture,
% 10.10/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 10.10/2.00      inference(cnf_transformation,[],[f88]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(c_34,plain,
% 10.10/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 10.10/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 10.10/2.00  
% 10.10/2.00  cnf(contradiction,plain,
% 10.10/2.00      ( $false ),
% 10.10/2.00      inference(minisat,
% 10.10/2.00                [status(thm)],
% 10.10/2.00                [c_25380,c_4067,c_38,c_36,c_35,c_34,c_33]) ).
% 10.10/2.00  
% 10.10/2.00  
% 10.10/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 10.10/2.00  
% 10.10/2.00  ------                               Statistics
% 10.10/2.00  
% 10.10/2.00  ------ General
% 10.10/2.00  
% 10.10/2.00  abstr_ref_over_cycles:                  0
% 10.10/2.00  abstr_ref_under_cycles:                 0
% 10.10/2.00  gc_basic_clause_elim:                   0
% 10.10/2.00  forced_gc_time:                         0
% 10.10/2.00  parsing_time:                           0.009
% 10.10/2.00  unif_index_cands_time:                  0.
% 10.10/2.00  unif_index_add_time:                    0.
% 10.10/2.00  orderings_time:                         0.
% 10.10/2.00  out_proof_time:                         0.022
% 10.10/2.00  total_time:                             1.192
% 10.10/2.00  num_of_symbols:                         56
% 10.10/2.00  num_of_terms:                           18259
% 10.10/2.00  
% 10.10/2.00  ------ Preprocessing
% 10.10/2.00  
% 10.10/2.00  num_of_splits:                          0
% 10.10/2.00  num_of_split_atoms:                     0
% 10.10/2.00  num_of_reused_defs:                     0
% 10.10/2.00  num_eq_ax_congr_red:                    51
% 10.10/2.00  num_of_sem_filtered_clauses:            6
% 10.10/2.00  num_of_subtypes:                        0
% 10.10/2.00  monotx_restored_types:                  0
% 10.10/2.00  sat_num_of_epr_types:                   0
% 10.10/2.00  sat_num_of_non_cyclic_types:            0
% 10.10/2.00  sat_guarded_non_collapsed_types:        0
% 10.10/2.00  num_pure_diseq_elim:                    0
% 10.10/2.00  simp_replaced_by:                       0
% 10.10/2.00  res_preprocessed:                       139
% 10.10/2.00  prep_upred:                             0
% 10.10/2.00  prep_unflattend:                        94
% 10.10/2.00  smt_new_axioms:                         0
% 10.10/2.00  pred_elim_cands:                        4
% 10.10/2.00  pred_elim:                              4
% 10.10/2.00  pred_elim_cl:                           9
% 10.10/2.00  pred_elim_cycles:                       7
% 10.10/2.00  merged_defs:                            0
% 10.10/2.00  merged_defs_ncl:                        0
% 10.10/2.00  bin_hyper_res:                          0
% 10.10/2.00  prep_cycles:                            5
% 10.10/2.00  pred_elim_time:                         0.021
% 10.10/2.00  splitting_time:                         0.
% 10.10/2.00  sem_filter_time:                        0.
% 10.10/2.00  monotx_time:                            0.001
% 10.10/2.00  subtype_inf_time:                       0.
% 10.10/2.00  
% 10.10/2.00  ------ Problem properties
% 10.10/2.00  
% 10.10/2.00  clauses:                                19
% 10.10/2.00  conjectures:                            6
% 10.10/2.00  epr:                                    5
% 10.10/2.00  horn:                                   19
% 10.10/2.00  ground:                                 6
% 10.10/2.00  unary:                                  8
% 10.10/2.00  binary:                                 2
% 10.10/2.00  lits:                                   49
% 10.10/2.00  lits_eq:                                6
% 10.10/2.00  fd_pure:                                0
% 10.10/2.00  fd_pseudo:                              0
% 10.10/2.00  fd_cond:                                0
% 10.10/2.00  fd_pseudo_cond:                         0
% 10.10/2.00  ac_symbols:                             0
% 10.10/2.00  
% 10.10/2.00  ------ Propositional Solver
% 10.10/2.00  
% 10.10/2.00  prop_solver_calls:                      34
% 10.10/2.00  prop_fast_solver_calls:                 2103
% 10.10/2.00  smt_solver_calls:                       0
% 10.10/2.00  smt_fast_solver_calls:                  0
% 10.10/2.00  prop_num_of_clauses:                    8749
% 10.10/2.00  prop_preprocess_simplified:             17534
% 10.10/2.00  prop_fo_subsumed:                       125
% 10.10/2.00  prop_solver_time:                       0.
% 10.10/2.00  smt_solver_time:                        0.
% 10.10/2.00  smt_fast_solver_time:                   0.
% 10.10/2.00  prop_fast_solver_time:                  0.
% 10.10/2.00  prop_unsat_core_time:                   0.001
% 10.10/2.00  
% 10.10/2.00  ------ QBF
% 10.10/2.00  
% 10.10/2.00  qbf_q_res:                              0
% 10.10/2.00  qbf_num_tautologies:                    0
% 10.10/2.00  qbf_prep_cycles:                        0
% 10.10/2.00  
% 10.10/2.00  ------ BMC1
% 10.10/2.00  
% 10.10/2.00  bmc1_current_bound:                     -1
% 10.10/2.00  bmc1_last_solved_bound:                 -1
% 10.10/2.00  bmc1_unsat_core_size:                   -1
% 10.10/2.00  bmc1_unsat_core_parents_size:           -1
% 10.10/2.00  bmc1_merge_next_fun:                    0
% 10.10/2.00  bmc1_unsat_core_clauses_time:           0.
% 10.10/2.00  
% 10.10/2.00  ------ Instantiation
% 10.10/2.00  
% 10.10/2.00  inst_num_of_clauses:                    2198
% 10.10/2.00  inst_num_in_passive:                    1134
% 10.10/2.00  inst_num_in_active:                     1025
% 10.10/2.00  inst_num_in_unprocessed:                39
% 10.10/2.00  inst_num_of_loops:                      1070
% 10.10/2.00  inst_num_of_learning_restarts:          0
% 10.10/2.00  inst_num_moves_active_passive:          42
% 10.10/2.00  inst_lit_activity:                      0
% 10.10/2.00  inst_lit_activity_moves:                1
% 10.10/2.00  inst_num_tautologies:                   0
% 10.10/2.00  inst_num_prop_implied:                  0
% 10.10/2.00  inst_num_existing_simplified:           0
% 10.10/2.00  inst_num_eq_res_simplified:             0
% 10.10/2.00  inst_num_child_elim:                    0
% 10.10/2.00  inst_num_of_dismatching_blockings:      839
% 10.10/2.00  inst_num_of_non_proper_insts:           2082
% 10.10/2.00  inst_num_of_duplicates:                 0
% 10.10/2.00  inst_inst_num_from_inst_to_res:         0
% 10.10/2.00  inst_dismatching_checking_time:         0.
% 10.10/2.00  
% 10.10/2.00  ------ Resolution
% 10.10/2.00  
% 10.10/2.00  res_num_of_clauses:                     0
% 10.10/2.00  res_num_in_passive:                     0
% 10.10/2.00  res_num_in_active:                      0
% 10.10/2.00  res_num_of_loops:                       144
% 10.10/2.00  res_forward_subset_subsumed:            144
% 10.10/2.00  res_backward_subset_subsumed:           0
% 10.10/2.00  res_forward_subsumed:                   0
% 10.10/2.00  res_backward_subsumed:                  0
% 10.10/2.00  res_forward_subsumption_resolution:     0
% 10.10/2.00  res_backward_subsumption_resolution:    0
% 10.10/2.00  res_clause_to_clause_subsumption:       2614
% 10.10/2.00  res_orphan_elimination:                 0
% 10.10/2.00  res_tautology_del:                      121
% 10.10/2.00  res_num_eq_res_simplified:              0
% 10.10/2.00  res_num_sel_changes:                    0
% 10.10/2.00  res_moves_from_active_to_pass:          0
% 10.10/2.00  
% 10.10/2.00  ------ Superposition
% 10.10/2.00  
% 10.10/2.00  sup_time_total:                         0.
% 10.10/2.00  sup_time_generating:                    0.
% 10.10/2.00  sup_time_sim_full:                      0.
% 10.10/2.00  sup_time_sim_immed:                     0.
% 10.10/2.00  
% 10.10/2.00  sup_num_of_clauses:                     756
% 10.10/2.00  sup_num_in_active:                      205
% 10.10/2.00  sup_num_in_passive:                     551
% 10.10/2.00  sup_num_of_loops:                       213
% 10.10/2.00  sup_fw_superposition:                   594
% 10.10/2.00  sup_bw_superposition:                   400
% 10.10/2.00  sup_immediate_simplified:               358
% 10.10/2.00  sup_given_eliminated:                   0
% 10.10/2.00  comparisons_done:                       0
% 10.10/2.00  comparisons_avoided:                    0
% 10.10/2.00  
% 10.10/2.00  ------ Simplifications
% 10.10/2.00  
% 10.10/2.00  
% 10.10/2.00  sim_fw_subset_subsumed:                 55
% 10.10/2.00  sim_bw_subset_subsumed:                 10
% 10.10/2.00  sim_fw_subsumed:                        73
% 10.10/2.00  sim_bw_subsumed:                        25
% 10.10/2.00  sim_fw_subsumption_res:                 5
% 10.10/2.00  sim_bw_subsumption_res:                 0
% 10.10/2.00  sim_tautology_del:                      12
% 10.10/2.00  sim_eq_tautology_del:                   24
% 10.10/2.00  sim_eq_res_simp:                        0
% 10.10/2.00  sim_fw_demodulated:                     23
% 10.10/2.00  sim_bw_demodulated:                     5
% 10.10/2.00  sim_light_normalised:                   256
% 10.10/2.00  sim_joinable_taut:                      0
% 10.10/2.00  sim_joinable_simp:                      0
% 10.10/2.00  sim_ac_normalised:                      0
% 10.10/2.00  sim_smt_subsumption:                    0
% 10.10/2.00  
%------------------------------------------------------------------------------
