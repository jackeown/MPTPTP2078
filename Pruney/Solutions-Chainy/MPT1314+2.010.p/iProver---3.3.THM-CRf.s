%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:42 EST 2020

% Result     : Theorem 11.05s
% Output     : CNFRefutation 11.05s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 832 expanded)
%              Number of clauses        :   68 ( 220 expanded)
%              Number of leaves         :   21 ( 262 expanded)
%              Depth                    :   18
%              Number of atoms          :  582 (4669 expanded)
%              Number of equality atoms :  172 ( 879 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
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
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f49,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v3_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(sK9,X2)
        & sK9 = X1
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v3_pre_topc(X3,sK8)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) )
        & v3_pre_topc(X1,X0)
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & sK7 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(sK7,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK6)
              & m1_pre_topc(X2,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ v3_pre_topc(sK9,sK8)
    & sK7 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v3_pre_topc(sK7,sK6)
    & m1_pre_topc(sK8,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f29,f49,f48,f47,f46])).

fof(f85,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f70,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f55])).

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
    inference(nnf_transformation,[],[f30])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f13,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK5(X0,X1,X2),X0)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f87,plain,(
    ~ v3_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    v3_pre_topc(sK9,sK6) ),
    inference(definition_unfolding,[],[f84,f86])).

fof(f82,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(definition_unfolding,[],[f82,f86])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2479,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_19,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_19])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_226,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_221,c_20])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_2474,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_4578,plain,
    ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_2474])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_777,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_778,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_2699,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8)
    | k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_4852,plain,
    ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4578,c_34,c_30,c_778,c_2699])).

cnf(c_2488,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3133,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_2488])).

cnf(c_35,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_39,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_779,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_2686,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2687,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2686])).

cnf(c_3504,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3133,c_35,c_39,c_779,c_2687])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_437,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_18,c_7])).

cnf(c_441,plain,
    ( ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_23])).

cnf(c_442,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_485,plain,
    ( ~ sP0(X0,X1)
    | k2_struct_0(X1) != X2
    | k2_struct_0(X0) != X3
    | k1_setfam_1(k2_tarski(X3,X2)) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_486,plain,
    ( ~ sP0(X0,X1)
    | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1274,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_442,c_486])).

cnf(c_2472,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_3510,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9))
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3504,c_2472])).

cnf(c_2791,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_4313,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3510,c_34,c_30,c_778,c_2686,c_2791])).

cnf(c_4855,plain,
    ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
    inference(demodulation,[status(thm)],[c_4852,c_4313])).

cnf(c_2477,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2486,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2919,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_2486])).

cnf(c_3154,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2919,c_35,c_779])).

cnf(c_22,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_393,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_22,c_21])).

cnf(c_2473,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2490,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3591,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) = k1_setfam_1(k2_tarski(X1,k2_struct_0(X0)))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2473,c_2490])).

cnf(c_6996,plain,
    ( k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))) ),
    inference(superposition,[status(thm)],[c_3154,c_3591])).

cnf(c_25,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2484,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7634,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6996,c_2484])).

cnf(c_7635,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7634,c_6996])).

cnf(c_39353,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))),sK8) = iProver_top
    | v3_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4855,c_7635])).

cnf(c_39388,plain,
    ( v3_pre_topc(sK9,X0) != iProver_top
    | v3_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_39353,c_4855])).

cnf(c_39402,plain,
    ( v3_pre_topc(sK9,sK6) != iProver_top
    | v3_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39388])).

cnf(c_29,negated_conjecture,
    ( ~ v3_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,plain,
    ( v3_pre_topc(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,negated_conjecture,
    ( v3_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,plain,
    ( v3_pre_topc(sK9,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39402,c_40,c_39,c_38,c_37,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.05/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.05/2.00  
% 11.05/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.05/2.00  
% 11.05/2.00  ------  iProver source info
% 11.05/2.00  
% 11.05/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.05/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.05/2.00  git: non_committed_changes: false
% 11.05/2.00  git: last_make_outside_of_git: false
% 11.05/2.00  
% 11.05/2.00  ------ 
% 11.05/2.00  
% 11.05/2.00  ------ Input Options
% 11.05/2.00  
% 11.05/2.00  --out_options                           all
% 11.05/2.00  --tptp_safe_out                         true
% 11.05/2.00  --problem_path                          ""
% 11.05/2.00  --include_path                          ""
% 11.05/2.00  --clausifier                            res/vclausify_rel
% 11.05/2.00  --clausifier_options                    --mode clausify
% 11.05/2.00  --stdin                                 false
% 11.05/2.00  --stats_out                             all
% 11.05/2.00  
% 11.05/2.00  ------ General Options
% 11.05/2.00  
% 11.05/2.00  --fof                                   false
% 11.05/2.00  --time_out_real                         305.
% 11.05/2.00  --time_out_virtual                      -1.
% 11.05/2.00  --symbol_type_check                     false
% 11.05/2.00  --clausify_out                          false
% 11.05/2.00  --sig_cnt_out                           false
% 11.05/2.00  --trig_cnt_out                          false
% 11.05/2.00  --trig_cnt_out_tolerance                1.
% 11.05/2.00  --trig_cnt_out_sk_spl                   false
% 11.05/2.00  --abstr_cl_out                          false
% 11.05/2.00  
% 11.05/2.00  ------ Global Options
% 11.05/2.00  
% 11.05/2.00  --schedule                              default
% 11.05/2.00  --add_important_lit                     false
% 11.05/2.00  --prop_solver_per_cl                    1000
% 11.05/2.00  --min_unsat_core                        false
% 11.05/2.00  --soft_assumptions                      false
% 11.05/2.00  --soft_lemma_size                       3
% 11.05/2.00  --prop_impl_unit_size                   0
% 11.05/2.00  --prop_impl_unit                        []
% 11.05/2.00  --share_sel_clauses                     true
% 11.05/2.00  --reset_solvers                         false
% 11.05/2.00  --bc_imp_inh                            [conj_cone]
% 11.05/2.00  --conj_cone_tolerance                   3.
% 11.05/2.00  --extra_neg_conj                        none
% 11.05/2.00  --large_theory_mode                     true
% 11.05/2.00  --prolific_symb_bound                   200
% 11.05/2.00  --lt_threshold                          2000
% 11.05/2.00  --clause_weak_htbl                      true
% 11.05/2.00  --gc_record_bc_elim                     false
% 11.05/2.00  
% 11.05/2.00  ------ Preprocessing Options
% 11.05/2.00  
% 11.05/2.00  --preprocessing_flag                    true
% 11.05/2.00  --time_out_prep_mult                    0.1
% 11.05/2.00  --splitting_mode                        input
% 11.05/2.00  --splitting_grd                         true
% 11.05/2.00  --splitting_cvd                         false
% 11.05/2.00  --splitting_cvd_svl                     false
% 11.05/2.00  --splitting_nvd                         32
% 11.05/2.00  --sub_typing                            true
% 11.05/2.00  --prep_gs_sim                           true
% 11.05/2.00  --prep_unflatten                        true
% 11.05/2.00  --prep_res_sim                          true
% 11.05/2.00  --prep_upred                            true
% 11.05/2.00  --prep_sem_filter                       exhaustive
% 11.05/2.00  --prep_sem_filter_out                   false
% 11.05/2.00  --pred_elim                             true
% 11.05/2.00  --res_sim_input                         true
% 11.05/2.00  --eq_ax_congr_red                       true
% 11.05/2.00  --pure_diseq_elim                       true
% 11.05/2.00  --brand_transform                       false
% 11.05/2.00  --non_eq_to_eq                          false
% 11.05/2.00  --prep_def_merge                        true
% 11.05/2.00  --prep_def_merge_prop_impl              false
% 11.05/2.00  --prep_def_merge_mbd                    true
% 11.05/2.00  --prep_def_merge_tr_red                 false
% 11.05/2.00  --prep_def_merge_tr_cl                  false
% 11.05/2.00  --smt_preprocessing                     true
% 11.05/2.00  --smt_ac_axioms                         fast
% 11.05/2.00  --preprocessed_out                      false
% 11.05/2.00  --preprocessed_stats                    false
% 11.05/2.00  
% 11.05/2.00  ------ Abstraction refinement Options
% 11.05/2.00  
% 11.05/2.00  --abstr_ref                             []
% 11.05/2.00  --abstr_ref_prep                        false
% 11.05/2.00  --abstr_ref_until_sat                   false
% 11.05/2.00  --abstr_ref_sig_restrict                funpre
% 11.05/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.05/2.00  --abstr_ref_under                       []
% 11.05/2.00  
% 11.05/2.00  ------ SAT Options
% 11.05/2.00  
% 11.05/2.00  --sat_mode                              false
% 11.05/2.00  --sat_fm_restart_options                ""
% 11.05/2.00  --sat_gr_def                            false
% 11.05/2.00  --sat_epr_types                         true
% 11.05/2.00  --sat_non_cyclic_types                  false
% 11.05/2.00  --sat_finite_models                     false
% 11.05/2.00  --sat_fm_lemmas                         false
% 11.05/2.00  --sat_fm_prep                           false
% 11.05/2.00  --sat_fm_uc_incr                        true
% 11.05/2.00  --sat_out_model                         small
% 11.05/2.00  --sat_out_clauses                       false
% 11.05/2.00  
% 11.05/2.00  ------ QBF Options
% 11.05/2.00  
% 11.05/2.00  --qbf_mode                              false
% 11.05/2.00  --qbf_elim_univ                         false
% 11.05/2.00  --qbf_dom_inst                          none
% 11.05/2.00  --qbf_dom_pre_inst                      false
% 11.05/2.00  --qbf_sk_in                             false
% 11.05/2.00  --qbf_pred_elim                         true
% 11.05/2.00  --qbf_split                             512
% 11.05/2.00  
% 11.05/2.00  ------ BMC1 Options
% 11.05/2.00  
% 11.05/2.00  --bmc1_incremental                      false
% 11.05/2.00  --bmc1_axioms                           reachable_all
% 11.05/2.00  --bmc1_min_bound                        0
% 11.05/2.00  --bmc1_max_bound                        -1
% 11.05/2.00  --bmc1_max_bound_default                -1
% 11.05/2.00  --bmc1_symbol_reachability              true
% 11.05/2.00  --bmc1_property_lemmas                  false
% 11.05/2.00  --bmc1_k_induction                      false
% 11.05/2.00  --bmc1_non_equiv_states                 false
% 11.05/2.00  --bmc1_deadlock                         false
% 11.05/2.00  --bmc1_ucm                              false
% 11.05/2.00  --bmc1_add_unsat_core                   none
% 11.05/2.00  --bmc1_unsat_core_children              false
% 11.05/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.05/2.00  --bmc1_out_stat                         full
% 11.05/2.00  --bmc1_ground_init                      false
% 11.05/2.00  --bmc1_pre_inst_next_state              false
% 11.05/2.00  --bmc1_pre_inst_state                   false
% 11.05/2.00  --bmc1_pre_inst_reach_state             false
% 11.05/2.00  --bmc1_out_unsat_core                   false
% 11.05/2.00  --bmc1_aig_witness_out                  false
% 11.05/2.00  --bmc1_verbose                          false
% 11.05/2.00  --bmc1_dump_clauses_tptp                false
% 11.05/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.05/2.00  --bmc1_dump_file                        -
% 11.05/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.05/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.05/2.00  --bmc1_ucm_extend_mode                  1
% 11.05/2.00  --bmc1_ucm_init_mode                    2
% 11.05/2.00  --bmc1_ucm_cone_mode                    none
% 11.05/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.05/2.00  --bmc1_ucm_relax_model                  4
% 11.05/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.05/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.05/2.00  --bmc1_ucm_layered_model                none
% 11.05/2.00  --bmc1_ucm_max_lemma_size               10
% 11.05/2.00  
% 11.05/2.00  ------ AIG Options
% 11.05/2.00  
% 11.05/2.00  --aig_mode                              false
% 11.05/2.00  
% 11.05/2.00  ------ Instantiation Options
% 11.05/2.00  
% 11.05/2.00  --instantiation_flag                    true
% 11.05/2.00  --inst_sos_flag                         false
% 11.05/2.00  --inst_sos_phase                        true
% 11.05/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.05/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.05/2.00  --inst_lit_sel_side                     num_symb
% 11.05/2.00  --inst_solver_per_active                1400
% 11.05/2.00  --inst_solver_calls_frac                1.
% 11.05/2.00  --inst_passive_queue_type               priority_queues
% 11.05/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.05/2.00  --inst_passive_queues_freq              [25;2]
% 11.05/2.00  --inst_dismatching                      true
% 11.05/2.00  --inst_eager_unprocessed_to_passive     true
% 11.05/2.00  --inst_prop_sim_given                   true
% 11.05/2.00  --inst_prop_sim_new                     false
% 11.05/2.00  --inst_subs_new                         false
% 11.05/2.00  --inst_eq_res_simp                      false
% 11.05/2.00  --inst_subs_given                       false
% 11.05/2.00  --inst_orphan_elimination               true
% 11.05/2.00  --inst_learning_loop_flag               true
% 11.05/2.00  --inst_learning_start                   3000
% 11.05/2.00  --inst_learning_factor                  2
% 11.05/2.00  --inst_start_prop_sim_after_learn       3
% 11.05/2.00  --inst_sel_renew                        solver
% 11.05/2.00  --inst_lit_activity_flag                true
% 11.05/2.00  --inst_restr_to_given                   false
% 11.05/2.00  --inst_activity_threshold               500
% 11.05/2.00  --inst_out_proof                        true
% 11.05/2.00  
% 11.05/2.00  ------ Resolution Options
% 11.05/2.00  
% 11.05/2.00  --resolution_flag                       true
% 11.05/2.00  --res_lit_sel                           adaptive
% 11.05/2.00  --res_lit_sel_side                      none
% 11.05/2.00  --res_ordering                          kbo
% 11.05/2.00  --res_to_prop_solver                    active
% 11.05/2.00  --res_prop_simpl_new                    false
% 11.05/2.00  --res_prop_simpl_given                  true
% 11.05/2.00  --res_passive_queue_type                priority_queues
% 11.05/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.05/2.00  --res_passive_queues_freq               [15;5]
% 11.05/2.00  --res_forward_subs                      full
% 11.05/2.00  --res_backward_subs                     full
% 11.05/2.00  --res_forward_subs_resolution           true
% 11.05/2.00  --res_backward_subs_resolution          true
% 11.05/2.00  --res_orphan_elimination                true
% 11.05/2.00  --res_time_limit                        2.
% 11.05/2.00  --res_out_proof                         true
% 11.05/2.00  
% 11.05/2.00  ------ Superposition Options
% 11.05/2.00  
% 11.05/2.00  --superposition_flag                    true
% 11.05/2.00  --sup_passive_queue_type                priority_queues
% 11.05/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.05/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.05/2.00  --demod_completeness_check              fast
% 11.05/2.00  --demod_use_ground                      true
% 11.05/2.00  --sup_to_prop_solver                    passive
% 11.05/2.00  --sup_prop_simpl_new                    true
% 11.05/2.00  --sup_prop_simpl_given                  true
% 11.05/2.00  --sup_fun_splitting                     false
% 11.05/2.00  --sup_smt_interval                      50000
% 11.05/2.00  
% 11.05/2.00  ------ Superposition Simplification Setup
% 11.05/2.00  
% 11.05/2.00  --sup_indices_passive                   []
% 11.05/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.05/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.05/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.05/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.05/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.05/2.00  --sup_full_bw                           [BwDemod]
% 11.05/2.00  --sup_immed_triv                        [TrivRules]
% 11.05/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.05/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.05/2.00  --sup_immed_bw_main                     []
% 11.05/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.05/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.05/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.05/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.05/2.00  
% 11.05/2.00  ------ Combination Options
% 11.05/2.00  
% 11.05/2.00  --comb_res_mult                         3
% 11.05/2.00  --comb_sup_mult                         2
% 11.05/2.00  --comb_inst_mult                        10
% 11.05/2.00  
% 11.05/2.00  ------ Debug Options
% 11.05/2.00  
% 11.05/2.00  --dbg_backtrace                         false
% 11.05/2.00  --dbg_dump_prop_clauses                 false
% 11.05/2.00  --dbg_dump_prop_clauses_file            -
% 11.05/2.00  --dbg_out_stat                          false
% 11.05/2.00  ------ Parsing...
% 11.05/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.05/2.00  
% 11.05/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.05/2.00  
% 11.05/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.05/2.00  
% 11.05/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.05/2.00  ------ Proving...
% 11.05/2.00  ------ Problem Properties 
% 11.05/2.00  
% 11.05/2.00  
% 11.05/2.00  clauses                                 21
% 11.05/2.00  conjectures                             6
% 11.05/2.00  EPR                                     5
% 11.05/2.00  Horn                                    21
% 11.05/2.00  unary                                   8
% 11.05/2.00  binary                                  2
% 11.05/2.00  lits                                    57
% 11.05/2.00  lits eq                                 6
% 11.05/2.00  fd_pure                                 0
% 11.05/2.00  fd_pseudo                               0
% 11.05/2.00  fd_cond                                 0
% 11.05/2.00  fd_pseudo_cond                          0
% 11.05/2.00  AC symbols                              0
% 11.05/2.00  
% 11.05/2.00  ------ Schedule dynamic 5 is on 
% 11.05/2.00  
% 11.05/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.05/2.00  
% 11.05/2.00  
% 11.05/2.00  ------ 
% 11.05/2.00  Current options:
% 11.05/2.00  ------ 
% 11.05/2.00  
% 11.05/2.00  ------ Input Options
% 11.05/2.00  
% 11.05/2.00  --out_options                           all
% 11.05/2.00  --tptp_safe_out                         true
% 11.05/2.00  --problem_path                          ""
% 11.05/2.00  --include_path                          ""
% 11.05/2.00  --clausifier                            res/vclausify_rel
% 11.05/2.00  --clausifier_options                    --mode clausify
% 11.05/2.00  --stdin                                 false
% 11.05/2.00  --stats_out                             all
% 11.05/2.00  
% 11.05/2.00  ------ General Options
% 11.05/2.00  
% 11.05/2.00  --fof                                   false
% 11.05/2.00  --time_out_real                         305.
% 11.05/2.00  --time_out_virtual                      -1.
% 11.05/2.00  --symbol_type_check                     false
% 11.05/2.00  --clausify_out                          false
% 11.05/2.00  --sig_cnt_out                           false
% 11.05/2.00  --trig_cnt_out                          false
% 11.05/2.00  --trig_cnt_out_tolerance                1.
% 11.05/2.00  --trig_cnt_out_sk_spl                   false
% 11.05/2.00  --abstr_cl_out                          false
% 11.05/2.00  
% 11.05/2.00  ------ Global Options
% 11.05/2.00  
% 11.05/2.00  --schedule                              default
% 11.05/2.00  --add_important_lit                     false
% 11.05/2.00  --prop_solver_per_cl                    1000
% 11.05/2.00  --min_unsat_core                        false
% 11.05/2.00  --soft_assumptions                      false
% 11.05/2.00  --soft_lemma_size                       3
% 11.05/2.00  --prop_impl_unit_size                   0
% 11.05/2.00  --prop_impl_unit                        []
% 11.05/2.00  --share_sel_clauses                     true
% 11.05/2.00  --reset_solvers                         false
% 11.05/2.00  --bc_imp_inh                            [conj_cone]
% 11.05/2.00  --conj_cone_tolerance                   3.
% 11.05/2.00  --extra_neg_conj                        none
% 11.05/2.00  --large_theory_mode                     true
% 11.05/2.00  --prolific_symb_bound                   200
% 11.05/2.00  --lt_threshold                          2000
% 11.05/2.00  --clause_weak_htbl                      true
% 11.05/2.00  --gc_record_bc_elim                     false
% 11.05/2.00  
% 11.05/2.00  ------ Preprocessing Options
% 11.05/2.00  
% 11.05/2.00  --preprocessing_flag                    true
% 11.05/2.00  --time_out_prep_mult                    0.1
% 11.05/2.00  --splitting_mode                        input
% 11.05/2.00  --splitting_grd                         true
% 11.05/2.00  --splitting_cvd                         false
% 11.05/2.00  --splitting_cvd_svl                     false
% 11.05/2.00  --splitting_nvd                         32
% 11.05/2.00  --sub_typing                            true
% 11.05/2.00  --prep_gs_sim                           true
% 11.05/2.00  --prep_unflatten                        true
% 11.05/2.00  --prep_res_sim                          true
% 11.05/2.00  --prep_upred                            true
% 11.05/2.00  --prep_sem_filter                       exhaustive
% 11.05/2.00  --prep_sem_filter_out                   false
% 11.05/2.00  --pred_elim                             true
% 11.05/2.00  --res_sim_input                         true
% 11.05/2.00  --eq_ax_congr_red                       true
% 11.05/2.00  --pure_diseq_elim                       true
% 11.05/2.00  --brand_transform                       false
% 11.05/2.00  --non_eq_to_eq                          false
% 11.05/2.00  --prep_def_merge                        true
% 11.05/2.00  --prep_def_merge_prop_impl              false
% 11.05/2.00  --prep_def_merge_mbd                    true
% 11.05/2.00  --prep_def_merge_tr_red                 false
% 11.05/2.00  --prep_def_merge_tr_cl                  false
% 11.05/2.00  --smt_preprocessing                     true
% 11.05/2.00  --smt_ac_axioms                         fast
% 11.05/2.00  --preprocessed_out                      false
% 11.05/2.00  --preprocessed_stats                    false
% 11.05/2.00  
% 11.05/2.00  ------ Abstraction refinement Options
% 11.05/2.00  
% 11.05/2.00  --abstr_ref                             []
% 11.05/2.00  --abstr_ref_prep                        false
% 11.05/2.00  --abstr_ref_until_sat                   false
% 11.05/2.00  --abstr_ref_sig_restrict                funpre
% 11.05/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.05/2.00  --abstr_ref_under                       []
% 11.05/2.00  
% 11.05/2.00  ------ SAT Options
% 11.05/2.00  
% 11.05/2.00  --sat_mode                              false
% 11.05/2.00  --sat_fm_restart_options                ""
% 11.05/2.00  --sat_gr_def                            false
% 11.05/2.00  --sat_epr_types                         true
% 11.05/2.00  --sat_non_cyclic_types                  false
% 11.05/2.00  --sat_finite_models                     false
% 11.05/2.00  --sat_fm_lemmas                         false
% 11.05/2.00  --sat_fm_prep                           false
% 11.05/2.00  --sat_fm_uc_incr                        true
% 11.05/2.00  --sat_out_model                         small
% 11.05/2.00  --sat_out_clauses                       false
% 11.05/2.00  
% 11.05/2.00  ------ QBF Options
% 11.05/2.00  
% 11.05/2.00  --qbf_mode                              false
% 11.05/2.00  --qbf_elim_univ                         false
% 11.05/2.00  --qbf_dom_inst                          none
% 11.05/2.00  --qbf_dom_pre_inst                      false
% 11.05/2.00  --qbf_sk_in                             false
% 11.05/2.00  --qbf_pred_elim                         true
% 11.05/2.00  --qbf_split                             512
% 11.05/2.00  
% 11.05/2.00  ------ BMC1 Options
% 11.05/2.00  
% 11.05/2.00  --bmc1_incremental                      false
% 11.05/2.00  --bmc1_axioms                           reachable_all
% 11.05/2.00  --bmc1_min_bound                        0
% 11.05/2.00  --bmc1_max_bound                        -1
% 11.05/2.00  --bmc1_max_bound_default                -1
% 11.05/2.00  --bmc1_symbol_reachability              true
% 11.05/2.00  --bmc1_property_lemmas                  false
% 11.05/2.00  --bmc1_k_induction                      false
% 11.05/2.00  --bmc1_non_equiv_states                 false
% 11.05/2.00  --bmc1_deadlock                         false
% 11.05/2.00  --bmc1_ucm                              false
% 11.05/2.00  --bmc1_add_unsat_core                   none
% 11.05/2.00  --bmc1_unsat_core_children              false
% 11.05/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.05/2.00  --bmc1_out_stat                         full
% 11.05/2.00  --bmc1_ground_init                      false
% 11.05/2.00  --bmc1_pre_inst_next_state              false
% 11.05/2.00  --bmc1_pre_inst_state                   false
% 11.05/2.00  --bmc1_pre_inst_reach_state             false
% 11.05/2.00  --bmc1_out_unsat_core                   false
% 11.05/2.00  --bmc1_aig_witness_out                  false
% 11.05/2.00  --bmc1_verbose                          false
% 11.05/2.00  --bmc1_dump_clauses_tptp                false
% 11.05/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.05/2.00  --bmc1_dump_file                        -
% 11.05/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.05/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.05/2.00  --bmc1_ucm_extend_mode                  1
% 11.05/2.00  --bmc1_ucm_init_mode                    2
% 11.05/2.00  --bmc1_ucm_cone_mode                    none
% 11.05/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.05/2.00  --bmc1_ucm_relax_model                  4
% 11.05/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.05/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.05/2.00  --bmc1_ucm_layered_model                none
% 11.05/2.00  --bmc1_ucm_max_lemma_size               10
% 11.05/2.00  
% 11.05/2.00  ------ AIG Options
% 11.05/2.00  
% 11.05/2.00  --aig_mode                              false
% 11.05/2.00  
% 11.05/2.00  ------ Instantiation Options
% 11.05/2.00  
% 11.05/2.00  --instantiation_flag                    true
% 11.05/2.00  --inst_sos_flag                         false
% 11.05/2.00  --inst_sos_phase                        true
% 11.05/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.05/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.05/2.00  --inst_lit_sel_side                     none
% 11.05/2.00  --inst_solver_per_active                1400
% 11.05/2.00  --inst_solver_calls_frac                1.
% 11.05/2.00  --inst_passive_queue_type               priority_queues
% 11.05/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.05/2.00  --inst_passive_queues_freq              [25;2]
% 11.05/2.00  --inst_dismatching                      true
% 11.05/2.00  --inst_eager_unprocessed_to_passive     true
% 11.05/2.00  --inst_prop_sim_given                   true
% 11.05/2.00  --inst_prop_sim_new                     false
% 11.05/2.00  --inst_subs_new                         false
% 11.05/2.00  --inst_eq_res_simp                      false
% 11.05/2.00  --inst_subs_given                       false
% 11.05/2.00  --inst_orphan_elimination               true
% 11.05/2.00  --inst_learning_loop_flag               true
% 11.05/2.00  --inst_learning_start                   3000
% 11.05/2.00  --inst_learning_factor                  2
% 11.05/2.00  --inst_start_prop_sim_after_learn       3
% 11.05/2.00  --inst_sel_renew                        solver
% 11.05/2.00  --inst_lit_activity_flag                true
% 11.05/2.00  --inst_restr_to_given                   false
% 11.05/2.00  --inst_activity_threshold               500
% 11.05/2.00  --inst_out_proof                        true
% 11.05/2.00  
% 11.05/2.00  ------ Resolution Options
% 11.05/2.00  
% 11.05/2.00  --resolution_flag                       false
% 11.05/2.00  --res_lit_sel                           adaptive
% 11.05/2.00  --res_lit_sel_side                      none
% 11.05/2.00  --res_ordering                          kbo
% 11.05/2.00  --res_to_prop_solver                    active
% 11.05/2.00  --res_prop_simpl_new                    false
% 11.05/2.00  --res_prop_simpl_given                  true
% 11.05/2.00  --res_passive_queue_type                priority_queues
% 11.05/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.05/2.00  --res_passive_queues_freq               [15;5]
% 11.05/2.00  --res_forward_subs                      full
% 11.05/2.00  --res_backward_subs                     full
% 11.05/2.00  --res_forward_subs_resolution           true
% 11.05/2.00  --res_backward_subs_resolution          true
% 11.05/2.00  --res_orphan_elimination                true
% 11.05/2.00  --res_time_limit                        2.
% 11.05/2.00  --res_out_proof                         true
% 11.05/2.00  
% 11.05/2.00  ------ Superposition Options
% 11.05/2.00  
% 11.05/2.00  --superposition_flag                    true
% 11.05/2.00  --sup_passive_queue_type                priority_queues
% 11.05/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.05/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.05/2.00  --demod_completeness_check              fast
% 11.05/2.00  --demod_use_ground                      true
% 11.05/2.00  --sup_to_prop_solver                    passive
% 11.05/2.00  --sup_prop_simpl_new                    true
% 11.05/2.00  --sup_prop_simpl_given                  true
% 11.05/2.00  --sup_fun_splitting                     false
% 11.05/2.00  --sup_smt_interval                      50000
% 11.05/2.00  
% 11.05/2.00  ------ Superposition Simplification Setup
% 11.05/2.00  
% 11.05/2.00  --sup_indices_passive                   []
% 11.05/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.05/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.05/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.05/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.05/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.05/2.00  --sup_full_bw                           [BwDemod]
% 11.05/2.00  --sup_immed_triv                        [TrivRules]
% 11.05/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.05/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.05/2.00  --sup_immed_bw_main                     []
% 11.05/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.05/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.05/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.05/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.05/2.00  
% 11.05/2.00  ------ Combination Options
% 11.05/2.00  
% 11.05/2.00  --comb_res_mult                         3
% 11.05/2.00  --comb_sup_mult                         2
% 11.05/2.00  --comb_inst_mult                        10
% 11.05/2.00  
% 11.05/2.00  ------ Debug Options
% 11.05/2.00  
% 11.05/2.00  --dbg_backtrace                         false
% 11.05/2.00  --dbg_dump_prop_clauses                 false
% 11.05/2.00  --dbg_dump_prop_clauses_file            -
% 11.05/2.00  --dbg_out_stat                          false
% 11.05/2.00  
% 11.05/2.00  
% 11.05/2.00  
% 11.05/2.00  
% 11.05/2.00  ------ Proving...
% 11.05/2.00  
% 11.05/2.00  
% 11.05/2.00  % SZS status Theorem for theBenchmark.p
% 11.05/2.00  
% 11.05/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.05/2.00  
% 11.05/2.00  fof(f14,conjecture,(
% 11.05/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f15,negated_conjecture,(
% 11.05/2.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 11.05/2.00    inference(negated_conjecture,[],[f14])).
% 11.05/2.00  
% 11.05/2.00  fof(f28,plain,(
% 11.05/2.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.05/2.00    inference(ennf_transformation,[],[f15])).
% 11.05/2.00  
% 11.05/2.00  fof(f29,plain,(
% 11.05/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.05/2.00    inference(flattening,[],[f28])).
% 11.05/2.00  
% 11.05/2.00  fof(f49,plain,(
% 11.05/2.00    ( ! [X2,X1] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v3_pre_topc(sK9,X2) & sK9 = X1 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 11.05/2.00    introduced(choice_axiom,[])).
% 11.05/2.00  
% 11.05/2.00  fof(f48,plain,(
% 11.05/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v3_pre_topc(X3,sK8) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) & v3_pre_topc(X1,X0) & m1_pre_topc(sK8,X0))) )),
% 11.05/2.00    introduced(choice_axiom,[])).
% 11.05/2.00  
% 11.05/2.00  fof(f47,plain,(
% 11.05/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK7,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.05/2.00    introduced(choice_axiom,[])).
% 11.05/2.00  
% 11.05/2.00  fof(f46,plain,(
% 11.05/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6))),
% 11.05/2.00    introduced(choice_axiom,[])).
% 11.05/2.00  
% 11.05/2.00  fof(f50,plain,(
% 11.05/2.00    (((~v3_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & v3_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6)),
% 11.05/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f29,f49,f48,f47,f46])).
% 11.05/2.00  
% 11.05/2.00  fof(f85,plain,(
% 11.05/2.00    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 11.05/2.00    inference(cnf_transformation,[],[f50])).
% 11.05/2.00  
% 11.05/2.00  fof(f6,axiom,(
% 11.05/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f18,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(ennf_transformation,[],[f6])).
% 11.05/2.00  
% 11.05/2.00  fof(f19,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(flattening,[],[f18])).
% 11.05/2.00  
% 11.05/2.00  fof(f33,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(nnf_transformation,[],[f19])).
% 11.05/2.00  
% 11.05/2.00  fof(f56,plain,(
% 11.05/2.00    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f33])).
% 11.05/2.00  
% 11.05/2.00  fof(f93,plain,(
% 11.05/2.00    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(equality_resolution,[],[f56])).
% 11.05/2.00  
% 11.05/2.00  fof(f8,axiom,(
% 11.05/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f21,plain,(
% 11.05/2.00    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.05/2.00    inference(ennf_transformation,[],[f8])).
% 11.05/2.00  
% 11.05/2.00  fof(f22,plain,(
% 11.05/2.00    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(flattening,[],[f21])).
% 11.05/2.00  
% 11.05/2.00  fof(f72,plain,(
% 11.05/2.00    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f22])).
% 11.05/2.00  
% 11.05/2.00  fof(f71,plain,(
% 11.05/2.00    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f22])).
% 11.05/2.00  
% 11.05/2.00  fof(f81,plain,(
% 11.05/2.00    l1_pre_topc(sK6)),
% 11.05/2.00    inference(cnf_transformation,[],[f50])).
% 11.05/2.00  
% 11.05/2.00  fof(f11,axiom,(
% 11.05/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f25,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(ennf_transformation,[],[f11])).
% 11.05/2.00  
% 11.05/2.00  fof(f75,plain,(
% 11.05/2.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f25])).
% 11.05/2.00  
% 11.05/2.00  fof(f83,plain,(
% 11.05/2.00    m1_pre_topc(sK8,sK6)),
% 11.05/2.00    inference(cnf_transformation,[],[f50])).
% 11.05/2.00  
% 11.05/2.00  fof(f7,axiom,(
% 11.05/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f20,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(ennf_transformation,[],[f7])).
% 11.05/2.00  
% 11.05/2.00  fof(f31,plain,(
% 11.05/2.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 11.05/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 11.05/2.00  
% 11.05/2.00  fof(f30,plain,(
% 11.05/2.00    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 11.05/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.05/2.00  
% 11.05/2.00  fof(f32,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(definition_folding,[],[f20,f31,f30])).
% 11.05/2.00  
% 11.05/2.00  fof(f70,plain,(
% 11.05/2.00    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f32])).
% 11.05/2.00  
% 11.05/2.00  fof(f34,plain,(
% 11.05/2.00    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 11.05/2.00    inference(nnf_transformation,[],[f31])).
% 11.05/2.00  
% 11.05/2.00  fof(f58,plain,(
% 11.05/2.00    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f34])).
% 11.05/2.00  
% 11.05/2.00  fof(f1,axiom,(
% 11.05/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f16,plain,(
% 11.05/2.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.05/2.00    inference(ennf_transformation,[],[f1])).
% 11.05/2.00  
% 11.05/2.00  fof(f51,plain,(
% 11.05/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f16])).
% 11.05/2.00  
% 11.05/2.00  fof(f5,axiom,(
% 11.05/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f55,plain,(
% 11.05/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.05/2.00    inference(cnf_transformation,[],[f5])).
% 11.05/2.00  
% 11.05/2.00  fof(f88,plain,(
% 11.05/2.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.05/2.00    inference(definition_unfolding,[],[f51,f55])).
% 11.05/2.00  
% 11.05/2.00  fof(f35,plain,(
% 11.05/2.00    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 11.05/2.00    inference(nnf_transformation,[],[f30])).
% 11.05/2.00  
% 11.05/2.00  fof(f36,plain,(
% 11.05/2.00    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 11.05/2.00    inference(flattening,[],[f35])).
% 11.05/2.00  
% 11.05/2.00  fof(f37,plain,(
% 11.05/2.00    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 11.05/2.00    inference(rectify,[],[f36])).
% 11.05/2.00  
% 11.05/2.00  fof(f40,plain,(
% 11.05/2.00    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 11.05/2.00    introduced(choice_axiom,[])).
% 11.05/2.00  
% 11.05/2.00  fof(f39,plain,(
% 11.05/2.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 11.05/2.00    introduced(choice_axiom,[])).
% 11.05/2.00  
% 11.05/2.00  fof(f38,plain,(
% 11.05/2.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.05/2.00    introduced(choice_axiom,[])).
% 11.05/2.00  
% 11.05/2.00  fof(f41,plain,(
% 11.05/2.00    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 11.05/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).
% 11.05/2.00  
% 11.05/2.00  fof(f60,plain,(
% 11.05/2.00    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f41])).
% 11.05/2.00  
% 11.05/2.00  fof(f10,axiom,(
% 11.05/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f24,plain,(
% 11.05/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(ennf_transformation,[],[f10])).
% 11.05/2.00  
% 11.05/2.00  fof(f74,plain,(
% 11.05/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f24])).
% 11.05/2.00  
% 11.05/2.00  fof(f9,axiom,(
% 11.05/2.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f23,plain,(
% 11.05/2.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 11.05/2.00    inference(ennf_transformation,[],[f9])).
% 11.05/2.00  
% 11.05/2.00  fof(f73,plain,(
% 11.05/2.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f23])).
% 11.05/2.00  
% 11.05/2.00  fof(f4,axiom,(
% 11.05/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f17,plain,(
% 11.05/2.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.05/2.00    inference(ennf_transformation,[],[f4])).
% 11.05/2.00  
% 11.05/2.00  fof(f54,plain,(
% 11.05/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.05/2.00    inference(cnf_transformation,[],[f17])).
% 11.05/2.00  
% 11.05/2.00  fof(f89,plain,(
% 11.05/2.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.05/2.00    inference(definition_unfolding,[],[f54,f55])).
% 11.05/2.00  
% 11.05/2.00  fof(f13,axiom,(
% 11.05/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 11.05/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.05/2.00  
% 11.05/2.00  fof(f27,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(ennf_transformation,[],[f13])).
% 11.05/2.00  
% 11.05/2.00  fof(f42,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(nnf_transformation,[],[f27])).
% 11.05/2.00  
% 11.05/2.00  fof(f43,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(rectify,[],[f42])).
% 11.05/2.00  
% 11.05/2.00  fof(f44,plain,(
% 11.05/2.00    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.05/2.00    introduced(choice_axiom,[])).
% 11.05/2.00  
% 11.05/2.00  fof(f45,plain,(
% 11.05/2.00    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.05/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).
% 11.05/2.00  
% 11.05/2.00  fof(f80,plain,(
% 11.05/2.00    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(cnf_transformation,[],[f45])).
% 11.05/2.00  
% 11.05/2.00  fof(f95,plain,(
% 11.05/2.00    ( ! [X0,X3,X1] : (v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.05/2.00    inference(equality_resolution,[],[f80])).
% 11.05/2.00  
% 11.05/2.00  fof(f87,plain,(
% 11.05/2.00    ~v3_pre_topc(sK9,sK8)),
% 11.05/2.00    inference(cnf_transformation,[],[f50])).
% 11.05/2.00  
% 11.05/2.00  fof(f84,plain,(
% 11.05/2.00    v3_pre_topc(sK7,sK6)),
% 11.05/2.00    inference(cnf_transformation,[],[f50])).
% 11.05/2.00  
% 11.05/2.00  fof(f86,plain,(
% 11.05/2.00    sK7 = sK9),
% 11.05/2.00    inference(cnf_transformation,[],[f50])).
% 11.05/2.00  
% 11.05/2.00  fof(f90,plain,(
% 11.05/2.00    v3_pre_topc(sK9,sK6)),
% 11.05/2.00    inference(definition_unfolding,[],[f84,f86])).
% 11.05/2.00  
% 11.05/2.00  fof(f82,plain,(
% 11.05/2.00    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 11.05/2.00    inference(cnf_transformation,[],[f50])).
% 11.05/2.00  
% 11.05/2.00  fof(f91,plain,(
% 11.05/2.00    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))),
% 11.05/2.00    inference(definition_unfolding,[],[f82,f86])).
% 11.05/2.00  
% 11.05/2.00  cnf(c_30,negated_conjecture,
% 11.05/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 11.05/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2479,plain,
% 11.05/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_5,plain,
% 11.05/2.00      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.05/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.05/2.00      | ~ l1_pre_topc(X0)
% 11.05/2.00      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 11.05/2.00      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 11.05/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_19,plain,
% 11.05/2.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.05/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.05/2.00      | ~ l1_pre_topc(X0) ),
% 11.05/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_220,plain,
% 11.05/2.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.05/2.00      | ~ l1_pre_topc(X0)
% 11.05/2.00      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 11.05/2.00      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 11.05/2.00      inference(global_propositional_subsumption,
% 11.05/2.00                [status(thm)],
% 11.05/2.00                [c_5,c_19]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_221,plain,
% 11.05/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.05/2.00      | ~ l1_pre_topc(X1)
% 11.05/2.00      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 11.05/2.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.05/2.00      inference(renaming,[status(thm)],[c_220]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_20,plain,
% 11.05/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.05/2.00      | ~ l1_pre_topc(X1)
% 11.05/2.00      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 11.05/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_226,plain,
% 11.05/2.00      ( ~ l1_pre_topc(X1)
% 11.05/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.05/2.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.05/2.00      inference(global_propositional_subsumption,
% 11.05/2.00                [status(thm)],
% 11.05/2.00                [c_221,c_20]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_227,plain,
% 11.05/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.05/2.00      | ~ l1_pre_topc(X1)
% 11.05/2.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.05/2.00      inference(renaming,[status(thm)],[c_226]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2474,plain,
% 11.05/2.00      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 11.05/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.05/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_4578,plain,
% 11.05/2.00      ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9
% 11.05/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 11.05/2.00      inference(superposition,[status(thm)],[c_2479,c_2474]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_34,negated_conjecture,
% 11.05/2.00      ( l1_pre_topc(sK6) ),
% 11.05/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_23,plain,
% 11.05/2.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.05/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_32,negated_conjecture,
% 11.05/2.00      ( m1_pre_topc(sK8,sK6) ),
% 11.05/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_777,plain,
% 11.05/2.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X0 | sK8 != X1 ),
% 11.05/2.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_778,plain,
% 11.05/2.00      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 11.05/2.00      inference(unflattening,[status(thm)],[c_777]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2699,plain,
% 11.05/2.00      ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 11.05/2.00      | ~ l1_pre_topc(sK8)
% 11.05/2.00      | k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
% 11.05/2.00      inference(instantiation,[status(thm)],[c_227]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_4852,plain,
% 11.05/2.00      ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
% 11.05/2.00      inference(global_propositional_subsumption,
% 11.05/2.00                [status(thm)],
% 11.05/2.00                [c_4578,c_34,c_30,c_778,c_2699]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2488,plain,
% 11.05/2.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 11.05/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.05/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_3133,plain,
% 11.05/2.00      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 11.05/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 11.05/2.00      inference(superposition,[status(thm)],[c_2479,c_2488]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_35,plain,
% 11.05/2.00      ( l1_pre_topc(sK6) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_39,plain,
% 11.05/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_779,plain,
% 11.05/2.00      ( l1_pre_topc(sK6) != iProver_top
% 11.05/2.00      | l1_pre_topc(sK8) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2686,plain,
% 11.05/2.00      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
% 11.05/2.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 11.05/2.00      | ~ l1_pre_topc(sK8) ),
% 11.05/2.00      inference(instantiation,[status(thm)],[c_19]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2687,plain,
% 11.05/2.00      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 11.05/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 11.05/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_2686]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_3504,plain,
% 11.05/2.00      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
% 11.05/2.00      inference(global_propositional_subsumption,
% 11.05/2.00                [status(thm)],
% 11.05/2.00                [c_3133,c_35,c_39,c_779,c_2687]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_18,plain,
% 11.05/2.00      ( sP1(X0,X1) | ~ l1_pre_topc(X0) | ~ l1_pre_topc(X1) ),
% 11.05/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_7,plain,
% 11.05/2.00      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 11.05/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_437,plain,
% 11.05/2.00      ( sP0(X0,X1)
% 11.05/2.00      | ~ m1_pre_topc(X0,X1)
% 11.05/2.00      | ~ l1_pre_topc(X0)
% 11.05/2.00      | ~ l1_pre_topc(X1) ),
% 11.05/2.00      inference(resolution,[status(thm)],[c_18,c_7]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_441,plain,
% 11.05/2.00      ( ~ m1_pre_topc(X0,X1) | sP0(X0,X1) | ~ l1_pre_topc(X1) ),
% 11.05/2.00      inference(global_propositional_subsumption,
% 11.05/2.00                [status(thm)],
% 11.05/2.00                [c_437,c_23]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_442,plain,
% 11.05/2.00      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 11.05/2.00      inference(renaming,[status(thm)],[c_441]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_0,plain,
% 11.05/2.00      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 11.05/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_17,plain,
% 11.05/2.00      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 11.05/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_485,plain,
% 11.05/2.00      ( ~ sP0(X0,X1)
% 11.05/2.00      | k2_struct_0(X1) != X2
% 11.05/2.00      | k2_struct_0(X0) != X3
% 11.05/2.00      | k1_setfam_1(k2_tarski(X3,X2)) = X3 ),
% 11.05/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_486,plain,
% 11.05/2.00      ( ~ sP0(X0,X1)
% 11.05/2.00      | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
% 11.05/2.00      inference(unflattening,[status(thm)],[c_485]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_1274,plain,
% 11.05/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.05/2.00      | ~ l1_pre_topc(X1)
% 11.05/2.00      | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
% 11.05/2.00      inference(resolution,[status(thm)],[c_442,c_486]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2472,plain,
% 11.05/2.00      ( k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
% 11.05/2.00      | m1_pre_topc(X0,X1) != iProver_top
% 11.05/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_3510,plain,
% 11.05/2.00      ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9))
% 11.05/2.00      | l1_pre_topc(sK8) != iProver_top ),
% 11.05/2.00      inference(superposition,[status(thm)],[c_3504,c_2472]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2791,plain,
% 11.05/2.00      ( ~ m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
% 11.05/2.00      | ~ l1_pre_topc(sK8)
% 11.05/2.00      | k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
% 11.05/2.00      inference(instantiation,[status(thm)],[c_1274]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_4313,plain,
% 11.05/2.00      ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
% 11.05/2.00      inference(global_propositional_subsumption,
% 11.05/2.00                [status(thm)],
% 11.05/2.00                [c_3510,c_34,c_30,c_778,c_2686,c_2791]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_4855,plain,
% 11.05/2.00      ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
% 11.05/2.00      inference(demodulation,[status(thm)],[c_4852,c_4313]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2477,plain,
% 11.05/2.00      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2486,plain,
% 11.05/2.00      ( m1_pre_topc(X0,X1) != iProver_top
% 11.05/2.00      | l1_pre_topc(X1) != iProver_top
% 11.05/2.00      | l1_pre_topc(X0) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2919,plain,
% 11.05/2.00      ( l1_pre_topc(sK6) != iProver_top
% 11.05/2.00      | l1_pre_topc(sK8) = iProver_top ),
% 11.05/2.00      inference(superposition,[status(thm)],[c_2477,c_2486]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_3154,plain,
% 11.05/2.00      ( l1_pre_topc(sK8) = iProver_top ),
% 11.05/2.00      inference(global_propositional_subsumption,
% 11.05/2.00                [status(thm)],
% 11.05/2.00                [c_2919,c_35,c_779]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_22,plain,
% 11.05/2.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 11.05/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_21,plain,
% 11.05/2.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 11.05/2.00      | ~ l1_struct_0(X0) ),
% 11.05/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_393,plain,
% 11.05/2.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 11.05/2.00      | ~ l1_pre_topc(X0) ),
% 11.05/2.00      inference(resolution,[status(thm)],[c_22,c_21]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2473,plain,
% 11.05/2.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 11.05/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_3,plain,
% 11.05/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.05/2.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 11.05/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2490,plain,
% 11.05/2.00      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 11.05/2.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_3591,plain,
% 11.05/2.00      ( k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) = k1_setfam_1(k2_tarski(X1,k2_struct_0(X0)))
% 11.05/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.05/2.00      inference(superposition,[status(thm)],[c_2473,c_2490]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_6996,plain,
% 11.05/2.00      ( k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) = k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))) ),
% 11.05/2.00      inference(superposition,[status(thm)],[c_3154,c_3591]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_25,plain,
% 11.05/2.00      ( ~ v3_pre_topc(X0,X1)
% 11.05/2.00      | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 11.05/2.00      | ~ m1_pre_topc(X2,X1)
% 11.05/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.05/2.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 11.05/2.00      | ~ l1_pre_topc(X1) ),
% 11.05/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_2484,plain,
% 11.05/2.00      ( v3_pre_topc(X0,X1) != iProver_top
% 11.05/2.00      | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
% 11.05/2.00      | m1_pre_topc(X2,X1) != iProver_top
% 11.05/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.05/2.00      | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 11.05/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_7634,plain,
% 11.05/2.00      ( v3_pre_topc(X0,X1) != iProver_top
% 11.05/2.00      | v3_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
% 11.05/2.00      | m1_pre_topc(sK8,X1) != iProver_top
% 11.05/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.05/2.00      | m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 11.05/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.05/2.00      inference(superposition,[status(thm)],[c_6996,c_2484]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_7635,plain,
% 11.05/2.00      ( v3_pre_topc(X0,X1) != iProver_top
% 11.05/2.00      | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),sK8) = iProver_top
% 11.05/2.00      | m1_pre_topc(sK8,X1) != iProver_top
% 11.05/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.05/2.00      | m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 11.05/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.05/2.00      inference(light_normalisation,[status(thm)],[c_7634,c_6996]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_39353,plain,
% 11.05/2.00      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))),sK8) = iProver_top
% 11.05/2.00      | v3_pre_topc(sK9,X0) != iProver_top
% 11.05/2.00      | m1_pre_topc(sK8,X0) != iProver_top
% 11.05/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.05/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 11.05/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.05/2.00      inference(superposition,[status(thm)],[c_4855,c_7635]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_39388,plain,
% 11.05/2.00      ( v3_pre_topc(sK9,X0) != iProver_top
% 11.05/2.00      | v3_pre_topc(sK9,sK8) = iProver_top
% 11.05/2.00      | m1_pre_topc(sK8,X0) != iProver_top
% 11.05/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.05/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 11.05/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.05/2.00      inference(light_normalisation,[status(thm)],[c_39353,c_4855]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_39402,plain,
% 11.05/2.00      ( v3_pre_topc(sK9,sK6) != iProver_top
% 11.05/2.00      | v3_pre_topc(sK9,sK8) = iProver_top
% 11.05/2.00      | m1_pre_topc(sK8,sK6) != iProver_top
% 11.05/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 11.05/2.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 11.05/2.00      | l1_pre_topc(sK6) != iProver_top ),
% 11.05/2.00      inference(instantiation,[status(thm)],[c_39388]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_29,negated_conjecture,
% 11.05/2.00      ( ~ v3_pre_topc(sK9,sK8) ),
% 11.05/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_40,plain,
% 11.05/2.00      ( v3_pre_topc(sK9,sK8) != iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_31,negated_conjecture,
% 11.05/2.00      ( v3_pre_topc(sK9,sK6) ),
% 11.05/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_38,plain,
% 11.05/2.00      ( v3_pre_topc(sK9,sK6) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_37,plain,
% 11.05/2.00      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_33,negated_conjecture,
% 11.05/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 11.05/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(c_36,plain,
% 11.05/2.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 11.05/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.05/2.00  
% 11.05/2.00  cnf(contradiction,plain,
% 11.05/2.00      ( $false ),
% 11.05/2.00      inference(minisat,
% 11.05/2.00                [status(thm)],
% 11.05/2.00                [c_39402,c_40,c_39,c_38,c_37,c_36,c_35]) ).
% 11.05/2.00  
% 11.05/2.00  
% 11.05/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.05/2.00  
% 11.05/2.00  ------                               Statistics
% 11.05/2.00  
% 11.05/2.00  ------ General
% 11.05/2.00  
% 11.05/2.00  abstr_ref_over_cycles:                  0
% 11.05/2.00  abstr_ref_under_cycles:                 0
% 11.05/2.00  gc_basic_clause_elim:                   0
% 11.05/2.00  forced_gc_time:                         0
% 11.05/2.00  parsing_time:                           0.01
% 11.05/2.00  unif_index_cands_time:                  0.
% 11.05/2.00  unif_index_add_time:                    0.
% 11.05/2.00  orderings_time:                         0.
% 11.05/2.00  out_proof_time:                         0.011
% 11.05/2.00  total_time:                             1.008
% 11.05/2.00  num_of_symbols:                         57
% 11.05/2.00  num_of_terms:                           28085
% 11.05/2.00  
% 11.05/2.00  ------ Preprocessing
% 11.05/2.00  
% 11.05/2.00  num_of_splits:                          0
% 11.05/2.00  num_of_split_atoms:                     0
% 11.05/2.00  num_of_reused_defs:                     0
% 11.05/2.00  num_eq_ax_congr_red:                    43
% 11.05/2.00  num_of_sem_filtered_clauses:            6
% 11.05/2.00  num_of_subtypes:                        0
% 11.05/2.00  monotx_restored_types:                  0
% 11.05/2.00  sat_num_of_epr_types:                   0
% 11.05/2.00  sat_num_of_non_cyclic_types:            0
% 11.05/2.00  sat_guarded_non_collapsed_types:        0
% 11.05/2.00  num_pure_diseq_elim:                    0
% 11.05/2.00  simp_replaced_by:                       0
% 11.05/2.00  res_preprocessed:                       155
% 11.05/2.00  prep_upred:                             0
% 11.05/2.00  prep_unflattend:                        109
% 11.05/2.00  smt_new_axioms:                         0
% 11.05/2.00  pred_elim_cands:                        5
% 11.05/2.00  pred_elim:                              4
% 11.05/2.00  pred_elim_cl:                           9
% 11.05/2.00  pred_elim_cycles:                       10
% 11.05/2.00  merged_defs:                            0
% 11.05/2.00  merged_defs_ncl:                        0
% 11.05/2.00  bin_hyper_res:                          0
% 11.05/2.00  prep_cycles:                            5
% 11.05/2.00  pred_elim_time:                         0.026
% 11.05/2.00  splitting_time:                         0.
% 11.05/2.00  sem_filter_time:                        0.
% 11.05/2.00  monotx_time:                            0.001
% 11.05/2.00  subtype_inf_time:                       0.
% 11.05/2.00  
% 11.05/2.00  ------ Problem properties
% 11.05/2.00  
% 11.05/2.00  clauses:                                21
% 11.05/2.00  conjectures:                            6
% 11.05/2.00  epr:                                    5
% 11.05/2.00  horn:                                   21
% 11.05/2.00  ground:                                 6
% 11.05/2.00  unary:                                  8
% 11.05/2.00  binary:                                 2
% 11.05/2.00  lits:                                   57
% 11.05/2.00  lits_eq:                                6
% 11.05/2.00  fd_pure:                                0
% 11.05/2.00  fd_pseudo:                              0
% 11.05/2.00  fd_cond:                                0
% 11.05/2.00  fd_pseudo_cond:                         0
% 11.05/2.00  ac_symbols:                             0
% 11.05/2.00  
% 11.05/2.00  ------ Propositional Solver
% 11.05/2.00  
% 11.05/2.00  prop_solver_calls:                      34
% 11.05/2.00  prop_fast_solver_calls:                 2377
% 11.05/2.00  smt_solver_calls:                       0
% 11.05/2.00  smt_fast_solver_calls:                  0
% 11.05/2.00  prop_num_of_clauses:                    12706
% 11.05/2.00  prop_preprocess_simplified:             24429
% 11.05/2.00  prop_fo_subsumed:                       151
% 11.05/2.00  prop_solver_time:                       0.
% 11.05/2.00  smt_solver_time:                        0.
% 11.05/2.00  smt_fast_solver_time:                   0.
% 11.05/2.00  prop_fast_solver_time:                  0.
% 11.05/2.00  prop_unsat_core_time:                   0.001
% 11.05/2.00  
% 11.05/2.00  ------ QBF
% 11.05/2.00  
% 11.05/2.00  qbf_q_res:                              0
% 11.05/2.00  qbf_num_tautologies:                    0
% 11.05/2.00  qbf_prep_cycles:                        0
% 11.05/2.00  
% 11.05/2.00  ------ BMC1
% 11.05/2.00  
% 11.05/2.00  bmc1_current_bound:                     -1
% 11.05/2.00  bmc1_last_solved_bound:                 -1
% 11.05/2.00  bmc1_unsat_core_size:                   -1
% 11.05/2.00  bmc1_unsat_core_parents_size:           -1
% 11.05/2.00  bmc1_merge_next_fun:                    0
% 11.05/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.05/2.00  
% 11.05/2.00  ------ Instantiation
% 11.05/2.00  
% 11.05/2.00  inst_num_of_clauses:                    3418
% 11.05/2.00  inst_num_in_passive:                    1141
% 11.05/2.00  inst_num_in_active:                     1455
% 11.05/2.00  inst_num_in_unprocessed:                822
% 11.05/2.00  inst_num_of_loops:                      1540
% 11.05/2.00  inst_num_of_learning_restarts:          0
% 11.05/2.00  inst_num_moves_active_passive:          80
% 11.05/2.00  inst_lit_activity:                      0
% 11.05/2.00  inst_lit_activity_moves:                1
% 11.05/2.00  inst_num_tautologies:                   0
% 11.05/2.00  inst_num_prop_implied:                  0
% 11.05/2.00  inst_num_existing_simplified:           0
% 11.05/2.00  inst_num_eq_res_simplified:             0
% 11.05/2.00  inst_num_child_elim:                    0
% 11.05/2.00  inst_num_of_dismatching_blockings:      1758
% 11.05/2.00  inst_num_of_non_proper_insts:           3190
% 11.05/2.00  inst_num_of_duplicates:                 0
% 11.05/2.00  inst_inst_num_from_inst_to_res:         0
% 11.05/2.00  inst_dismatching_checking_time:         0.
% 11.05/2.00  
% 11.05/2.00  ------ Resolution
% 11.05/2.00  
% 11.05/2.00  res_num_of_clauses:                     0
% 11.05/2.00  res_num_in_passive:                     0
% 11.05/2.00  res_num_in_active:                      0
% 11.05/2.00  res_num_of_loops:                       160
% 11.05/2.00  res_forward_subset_subsumed:            290
% 11.05/2.00  res_backward_subset_subsumed:           8
% 11.05/2.00  res_forward_subsumed:                   0
% 11.05/2.00  res_backward_subsumed:                  0
% 11.05/2.00  res_forward_subsumption_resolution:     0
% 11.05/2.00  res_backward_subsumption_resolution:    0
% 11.05/2.00  res_clause_to_clause_subsumption:       5473
% 11.05/2.00  res_orphan_elimination:                 0
% 11.05/2.00  res_tautology_del:                      200
% 11.05/2.00  res_num_eq_res_simplified:              0
% 11.05/2.00  res_num_sel_changes:                    0
% 11.05/2.00  res_moves_from_active_to_pass:          0
% 11.05/2.00  
% 11.05/2.00  ------ Superposition
% 11.05/2.00  
% 11.05/2.00  sup_time_total:                         0.
% 11.05/2.00  sup_time_generating:                    0.
% 11.05/2.00  sup_time_sim_full:                      0.
% 11.05/2.00  sup_time_sim_immed:                     0.
% 11.05/2.00  
% 11.05/2.00  sup_num_of_clauses:                     1326
% 11.05/2.00  sup_num_in_active:                      296
% 11.05/2.00  sup_num_in_passive:                     1030
% 11.05/2.00  sup_num_of_loops:                       306
% 11.05/2.00  sup_fw_superposition:                   876
% 11.05/2.00  sup_bw_superposition:                   945
% 11.05/2.00  sup_immediate_simplified:               669
% 11.05/2.00  sup_given_eliminated:                   0
% 11.05/2.00  comparisons_done:                       0
% 11.05/2.00  comparisons_avoided:                    0
% 11.05/2.00  
% 11.05/2.00  ------ Simplifications
% 11.05/2.00  
% 11.05/2.00  
% 11.05/2.00  sim_fw_subset_subsumed:                 187
% 11.05/2.00  sim_bw_subset_subsumed:                 16
% 11.05/2.00  sim_fw_subsumed:                        148
% 11.05/2.00  sim_bw_subsumed:                        10
% 11.05/2.00  sim_fw_subsumption_res:                 6
% 11.05/2.00  sim_bw_subsumption_res:                 18
% 11.05/2.00  sim_tautology_del:                      9
% 11.05/2.00  sim_eq_tautology_del:                   63
% 11.05/2.00  sim_eq_res_simp:                        0
% 11.05/2.00  sim_fw_demodulated:                     22
% 11.05/2.00  sim_bw_demodulated:                     11
% 11.05/2.00  sim_light_normalised:                   342
% 11.05/2.00  sim_joinable_taut:                      0
% 11.05/2.00  sim_joinable_simp:                      0
% 11.05/2.00  sim_ac_normalised:                      0
% 11.05/2.00  sim_smt_subsumption:                    0
% 11.05/2.00  
%------------------------------------------------------------------------------
