%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:42 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  151 (1077 expanded)
%              Number of clauses        :   75 ( 305 expanded)
%              Number of leaves         :   23 ( 341 expanded)
%              Depth                    :   20
%              Number of atoms          :  598 (5827 expanded)
%              Number of equality atoms :  192 (1138 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v3_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(sK9,X2)
        & sK9 = X1
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f48,plain,
    ( ~ v3_pre_topc(sK9,sK8)
    & sK7 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v3_pre_topc(sK7,sK6)
    & m1_pre_topc(sK8,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f27,f47,f46,f45,f44])).

fof(f80,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f29,f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f28])).

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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f84,plain,(
    ~ v3_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    v3_pre_topc(sK9,sK6) ),
    inference(definition_unfolding,[],[f81,f83])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(definition_unfolding,[],[f79,f83])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2307,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2315,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2696,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_2315])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_716,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_717,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_718,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_2927,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2696,c_34,c_718])).

cnf(c_22,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_384,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_22,c_6])).

cnf(c_2303,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_3387,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_2927,c_2303])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2309,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3879,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3387,c_2309])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_20,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_20])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_221,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_21])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_221])).

cnf(c_2304,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_4194,plain,
    ( k2_struct_0(k1_pre_topc(sK8,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3387,c_2304])).

cnf(c_7421,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | k2_struct_0(k1_pre_topc(sK8,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4194,c_34,c_718])).

cnf(c_7422,plain,
    ( k2_struct_0(k1_pre_topc(sK8,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7421])).

cnf(c_7430,plain,
    ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
    inference(superposition,[status(thm)],[c_3879,c_7422])).

cnf(c_2317,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2906,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_2317])).

cnf(c_38,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2495,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2496,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2495])).

cnf(c_3244,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2906,c_34,c_38,c_718,c_2496])).

cnf(c_19,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_428,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_19,c_8])).

cnf(c_432,plain,
    ( ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_23])).

cnf(c_433,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_432])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_476,plain,
    ( ~ sP0(X0,X1)
    | k2_struct_0(X1) != X2
    | k2_struct_0(X0) != X3
    | k1_setfam_1(k2_tarski(X3,X2)) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_477,plain,
    ( ~ sP0(X0,X1)
    | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_1196,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_433,c_477])).

cnf(c_2302,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1196])).

cnf(c_3250,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9))
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3244,c_2302])).

cnf(c_2586,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
    | ~ l1_pre_topc(sK8)
    | k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_4469,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3250,c_33,c_29,c_717,c_2495,c_2586])).

cnf(c_7513,plain,
    ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
    inference(demodulation,[status(thm)],[c_7430,c_4469])).

cnf(c_24,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2314,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4243,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3387,c_2314])).

cnf(c_4264,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4243,c_3387])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2320,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2335,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2320,c_1])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2319,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2767,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2335,c_2319])).

cnf(c_10451,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),sK8) = iProver_top
    | m1_pre_topc(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4264,c_2767])).

cnf(c_10461,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))),sK8) = iProver_top
    | v3_pre_topc(sK9,X0) != iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7513,c_10451])).

cnf(c_10462,plain,
    ( v3_pre_topc(sK9,X0) != iProver_top
    | v3_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10461,c_7513])).

cnf(c_10464,plain,
    ( v3_pre_topc(sK9,sK6) != iProver_top
    | v3_pre_topc(sK9,sK8) = iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10462])).

cnf(c_28,negated_conjecture,
    ( ~ v3_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,plain,
    ( v3_pre_topc(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,negated_conjecture,
    ( v3_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,plain,
    ( v3_pre_topc(sK9,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10464,c_3879,c_39,c_37,c_36,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:35:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.51/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.98  
% 3.51/0.98  ------  iProver source info
% 3.51/0.98  
% 3.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.98  git: non_committed_changes: false
% 3.51/0.98  git: last_make_outside_of_git: false
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options
% 3.51/0.98  
% 3.51/0.98  --out_options                           all
% 3.51/0.98  --tptp_safe_out                         true
% 3.51/0.98  --problem_path                          ""
% 3.51/0.98  --include_path                          ""
% 3.51/0.98  --clausifier                            res/vclausify_rel
% 3.51/0.98  --clausifier_options                    --mode clausify
% 3.51/0.98  --stdin                                 false
% 3.51/0.98  --stats_out                             all
% 3.51/0.98  
% 3.51/0.98  ------ General Options
% 3.51/0.98  
% 3.51/0.98  --fof                                   false
% 3.51/0.98  --time_out_real                         305.
% 3.51/0.98  --time_out_virtual                      -1.
% 3.51/0.98  --symbol_type_check                     false
% 3.51/0.98  --clausify_out                          false
% 3.51/0.98  --sig_cnt_out                           false
% 3.51/0.98  --trig_cnt_out                          false
% 3.51/0.98  --trig_cnt_out_tolerance                1.
% 3.51/0.98  --trig_cnt_out_sk_spl                   false
% 3.51/0.98  --abstr_cl_out                          false
% 3.51/0.98  
% 3.51/0.98  ------ Global Options
% 3.51/0.98  
% 3.51/0.98  --schedule                              default
% 3.51/0.98  --add_important_lit                     false
% 3.51/0.98  --prop_solver_per_cl                    1000
% 3.51/0.98  --min_unsat_core                        false
% 3.51/0.98  --soft_assumptions                      false
% 3.51/0.98  --soft_lemma_size                       3
% 3.51/0.98  --prop_impl_unit_size                   0
% 3.51/0.98  --prop_impl_unit                        []
% 3.51/0.98  --share_sel_clauses                     true
% 3.51/0.98  --reset_solvers                         false
% 3.51/0.98  --bc_imp_inh                            [conj_cone]
% 3.51/0.98  --conj_cone_tolerance                   3.
% 3.51/0.98  --extra_neg_conj                        none
% 3.51/0.98  --large_theory_mode                     true
% 3.51/0.98  --prolific_symb_bound                   200
% 3.51/0.98  --lt_threshold                          2000
% 3.51/0.98  --clause_weak_htbl                      true
% 3.51/0.98  --gc_record_bc_elim                     false
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing Options
% 3.51/0.98  
% 3.51/0.98  --preprocessing_flag                    true
% 3.51/0.98  --time_out_prep_mult                    0.1
% 3.51/0.98  --splitting_mode                        input
% 3.51/0.98  --splitting_grd                         true
% 3.51/0.98  --splitting_cvd                         false
% 3.51/0.98  --splitting_cvd_svl                     false
% 3.51/0.98  --splitting_nvd                         32
% 3.51/0.98  --sub_typing                            true
% 3.51/0.98  --prep_gs_sim                           true
% 3.51/0.98  --prep_unflatten                        true
% 3.51/0.98  --prep_res_sim                          true
% 3.51/0.98  --prep_upred                            true
% 3.51/0.98  --prep_sem_filter                       exhaustive
% 3.51/0.98  --prep_sem_filter_out                   false
% 3.51/0.98  --pred_elim                             true
% 3.51/0.98  --res_sim_input                         true
% 3.51/0.98  --eq_ax_congr_red                       true
% 3.51/0.98  --pure_diseq_elim                       true
% 3.51/0.98  --brand_transform                       false
% 3.51/0.98  --non_eq_to_eq                          false
% 3.51/0.98  --prep_def_merge                        true
% 3.51/0.98  --prep_def_merge_prop_impl              false
% 3.51/0.98  --prep_def_merge_mbd                    true
% 3.51/0.98  --prep_def_merge_tr_red                 false
% 3.51/0.98  --prep_def_merge_tr_cl                  false
% 3.51/0.98  --smt_preprocessing                     true
% 3.51/0.98  --smt_ac_axioms                         fast
% 3.51/0.98  --preprocessed_out                      false
% 3.51/0.98  --preprocessed_stats                    false
% 3.51/0.98  
% 3.51/0.98  ------ Abstraction refinement Options
% 3.51/0.98  
% 3.51/0.98  --abstr_ref                             []
% 3.51/0.98  --abstr_ref_prep                        false
% 3.51/0.98  --abstr_ref_until_sat                   false
% 3.51/0.98  --abstr_ref_sig_restrict                funpre
% 3.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.98  --abstr_ref_under                       []
% 3.51/0.98  
% 3.51/0.98  ------ SAT Options
% 3.51/0.98  
% 3.51/0.98  --sat_mode                              false
% 3.51/0.98  --sat_fm_restart_options                ""
% 3.51/0.98  --sat_gr_def                            false
% 3.51/0.98  --sat_epr_types                         true
% 3.51/0.98  --sat_non_cyclic_types                  false
% 3.51/0.98  --sat_finite_models                     false
% 3.51/0.98  --sat_fm_lemmas                         false
% 3.51/0.98  --sat_fm_prep                           false
% 3.51/0.98  --sat_fm_uc_incr                        true
% 3.51/0.98  --sat_out_model                         small
% 3.51/0.98  --sat_out_clauses                       false
% 3.51/0.98  
% 3.51/0.98  ------ QBF Options
% 3.51/0.98  
% 3.51/0.98  --qbf_mode                              false
% 3.51/0.98  --qbf_elim_univ                         false
% 3.51/0.98  --qbf_dom_inst                          none
% 3.51/0.98  --qbf_dom_pre_inst                      false
% 3.51/0.98  --qbf_sk_in                             false
% 3.51/0.98  --qbf_pred_elim                         true
% 3.51/0.98  --qbf_split                             512
% 3.51/0.98  
% 3.51/0.98  ------ BMC1 Options
% 3.51/0.98  
% 3.51/0.98  --bmc1_incremental                      false
% 3.51/0.98  --bmc1_axioms                           reachable_all
% 3.51/0.98  --bmc1_min_bound                        0
% 3.51/0.98  --bmc1_max_bound                        -1
% 3.51/0.98  --bmc1_max_bound_default                -1
% 3.51/0.98  --bmc1_symbol_reachability              true
% 3.51/0.98  --bmc1_property_lemmas                  false
% 3.51/0.98  --bmc1_k_induction                      false
% 3.51/0.98  --bmc1_non_equiv_states                 false
% 3.51/0.98  --bmc1_deadlock                         false
% 3.51/0.98  --bmc1_ucm                              false
% 3.51/0.98  --bmc1_add_unsat_core                   none
% 3.51/0.98  --bmc1_unsat_core_children              false
% 3.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.98  --bmc1_out_stat                         full
% 3.51/0.98  --bmc1_ground_init                      false
% 3.51/0.98  --bmc1_pre_inst_next_state              false
% 3.51/0.98  --bmc1_pre_inst_state                   false
% 3.51/0.98  --bmc1_pre_inst_reach_state             false
% 3.51/0.98  --bmc1_out_unsat_core                   false
% 3.51/0.98  --bmc1_aig_witness_out                  false
% 3.51/0.98  --bmc1_verbose                          false
% 3.51/0.98  --bmc1_dump_clauses_tptp                false
% 3.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.98  --bmc1_dump_file                        -
% 3.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.98  --bmc1_ucm_extend_mode                  1
% 3.51/0.98  --bmc1_ucm_init_mode                    2
% 3.51/0.98  --bmc1_ucm_cone_mode                    none
% 3.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.98  --bmc1_ucm_relax_model                  4
% 3.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.98  --bmc1_ucm_layered_model                none
% 3.51/0.98  --bmc1_ucm_max_lemma_size               10
% 3.51/0.98  
% 3.51/0.98  ------ AIG Options
% 3.51/0.98  
% 3.51/0.98  --aig_mode                              false
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation Options
% 3.51/0.98  
% 3.51/0.98  --instantiation_flag                    true
% 3.51/0.98  --inst_sos_flag                         false
% 3.51/0.98  --inst_sos_phase                        true
% 3.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel_side                     num_symb
% 3.51/0.98  --inst_solver_per_active                1400
% 3.51/0.98  --inst_solver_calls_frac                1.
% 3.51/0.98  --inst_passive_queue_type               priority_queues
% 3.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.98  --inst_passive_queues_freq              [25;2]
% 3.51/0.98  --inst_dismatching                      true
% 3.51/0.98  --inst_eager_unprocessed_to_passive     true
% 3.51/0.98  --inst_prop_sim_given                   true
% 3.51/0.98  --inst_prop_sim_new                     false
% 3.51/0.98  --inst_subs_new                         false
% 3.51/0.98  --inst_eq_res_simp                      false
% 3.51/0.98  --inst_subs_given                       false
% 3.51/0.98  --inst_orphan_elimination               true
% 3.51/0.98  --inst_learning_loop_flag               true
% 3.51/0.98  --inst_learning_start                   3000
% 3.51/0.98  --inst_learning_factor                  2
% 3.51/0.98  --inst_start_prop_sim_after_learn       3
% 3.51/0.98  --inst_sel_renew                        solver
% 3.51/0.98  --inst_lit_activity_flag                true
% 3.51/0.98  --inst_restr_to_given                   false
% 3.51/0.98  --inst_activity_threshold               500
% 3.51/0.98  --inst_out_proof                        true
% 3.51/0.98  
% 3.51/0.98  ------ Resolution Options
% 3.51/0.98  
% 3.51/0.98  --resolution_flag                       true
% 3.51/0.98  --res_lit_sel                           adaptive
% 3.51/0.98  --res_lit_sel_side                      none
% 3.51/0.98  --res_ordering                          kbo
% 3.51/0.98  --res_to_prop_solver                    active
% 3.51/0.98  --res_prop_simpl_new                    false
% 3.51/0.98  --res_prop_simpl_given                  true
% 3.51/0.98  --res_passive_queue_type                priority_queues
% 3.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.98  --res_passive_queues_freq               [15;5]
% 3.51/0.98  --res_forward_subs                      full
% 3.51/0.98  --res_backward_subs                     full
% 3.51/0.98  --res_forward_subs_resolution           true
% 3.51/0.98  --res_backward_subs_resolution          true
% 3.51/0.98  --res_orphan_elimination                true
% 3.51/0.98  --res_time_limit                        2.
% 3.51/0.98  --res_out_proof                         true
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Options
% 3.51/0.98  
% 3.51/0.98  --superposition_flag                    true
% 3.51/0.98  --sup_passive_queue_type                priority_queues
% 3.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.98  --demod_completeness_check              fast
% 3.51/0.98  --demod_use_ground                      true
% 3.51/0.98  --sup_to_prop_solver                    passive
% 3.51/0.98  --sup_prop_simpl_new                    true
% 3.51/0.98  --sup_prop_simpl_given                  true
% 3.51/0.98  --sup_fun_splitting                     false
% 3.51/0.98  --sup_smt_interval                      50000
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Simplification Setup
% 3.51/0.98  
% 3.51/0.98  --sup_indices_passive                   []
% 3.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.98  --sup_full_bw                           [BwDemod]
% 3.51/0.98  --sup_immed_triv                        [TrivRules]
% 3.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.98  --sup_immed_bw_main                     []
% 3.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.98  
% 3.51/0.98  ------ Combination Options
% 3.51/0.98  
% 3.51/0.98  --comb_res_mult                         3
% 3.51/0.98  --comb_sup_mult                         2
% 3.51/0.98  --comb_inst_mult                        10
% 3.51/0.98  
% 3.51/0.98  ------ Debug Options
% 3.51/0.98  
% 3.51/0.98  --dbg_backtrace                         false
% 3.51/0.98  --dbg_dump_prop_clauses                 false
% 3.51/0.98  --dbg_dump_prop_clauses_file            -
% 3.51/0.98  --dbg_out_stat                          false
% 3.51/0.98  ------ Parsing...
% 3.51/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.98  ------ Proving...
% 3.51/0.98  ------ Problem Properties 
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  clauses                                 20
% 3.51/0.98  conjectures                             6
% 3.51/0.98  EPR                                     5
% 3.51/0.98  Horn                                    20
% 3.51/0.98  unary                                   8
% 3.51/0.98  binary                                  2
% 3.51/0.98  lits                                    53
% 3.51/0.98  lits eq                                 7
% 3.51/0.98  fd_pure                                 0
% 3.51/0.98  fd_pseudo                               0
% 3.51/0.98  fd_cond                                 0
% 3.51/0.98  fd_pseudo_cond                          0
% 3.51/0.98  AC symbols                              0
% 3.51/0.98  
% 3.51/0.98  ------ Schedule dynamic 5 is on 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  Current options:
% 3.51/0.98  ------ 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options
% 3.51/0.98  
% 3.51/0.98  --out_options                           all
% 3.51/0.98  --tptp_safe_out                         true
% 3.51/0.98  --problem_path                          ""
% 3.51/0.98  --include_path                          ""
% 3.51/0.98  --clausifier                            res/vclausify_rel
% 3.51/0.98  --clausifier_options                    --mode clausify
% 3.51/0.98  --stdin                                 false
% 3.51/0.98  --stats_out                             all
% 3.51/0.98  
% 3.51/0.98  ------ General Options
% 3.51/0.98  
% 3.51/0.98  --fof                                   false
% 3.51/0.98  --time_out_real                         305.
% 3.51/0.98  --time_out_virtual                      -1.
% 3.51/0.98  --symbol_type_check                     false
% 3.51/0.98  --clausify_out                          false
% 3.51/0.98  --sig_cnt_out                           false
% 3.51/0.98  --trig_cnt_out                          false
% 3.51/0.98  --trig_cnt_out_tolerance                1.
% 3.51/0.98  --trig_cnt_out_sk_spl                   false
% 3.51/0.98  --abstr_cl_out                          false
% 3.51/0.98  
% 3.51/0.98  ------ Global Options
% 3.51/0.98  
% 3.51/0.98  --schedule                              default
% 3.51/0.98  --add_important_lit                     false
% 3.51/0.98  --prop_solver_per_cl                    1000
% 3.51/0.98  --min_unsat_core                        false
% 3.51/0.98  --soft_assumptions                      false
% 3.51/0.98  --soft_lemma_size                       3
% 3.51/0.98  --prop_impl_unit_size                   0
% 3.51/0.98  --prop_impl_unit                        []
% 3.51/0.98  --share_sel_clauses                     true
% 3.51/0.98  --reset_solvers                         false
% 3.51/0.98  --bc_imp_inh                            [conj_cone]
% 3.51/0.98  --conj_cone_tolerance                   3.
% 3.51/0.98  --extra_neg_conj                        none
% 3.51/0.98  --large_theory_mode                     true
% 3.51/0.98  --prolific_symb_bound                   200
% 3.51/0.98  --lt_threshold                          2000
% 3.51/0.98  --clause_weak_htbl                      true
% 3.51/0.98  --gc_record_bc_elim                     false
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing Options
% 3.51/0.98  
% 3.51/0.98  --preprocessing_flag                    true
% 3.51/0.98  --time_out_prep_mult                    0.1
% 3.51/0.98  --splitting_mode                        input
% 3.51/0.98  --splitting_grd                         true
% 3.51/0.98  --splitting_cvd                         false
% 3.51/0.98  --splitting_cvd_svl                     false
% 3.51/0.98  --splitting_nvd                         32
% 3.51/0.98  --sub_typing                            true
% 3.51/0.98  --prep_gs_sim                           true
% 3.51/0.98  --prep_unflatten                        true
% 3.51/0.98  --prep_res_sim                          true
% 3.51/0.98  --prep_upred                            true
% 3.51/0.98  --prep_sem_filter                       exhaustive
% 3.51/0.98  --prep_sem_filter_out                   false
% 3.51/0.98  --pred_elim                             true
% 3.51/0.98  --res_sim_input                         true
% 3.51/0.98  --eq_ax_congr_red                       true
% 3.51/0.98  --pure_diseq_elim                       true
% 3.51/0.98  --brand_transform                       false
% 3.51/0.98  --non_eq_to_eq                          false
% 3.51/0.98  --prep_def_merge                        true
% 3.51/0.98  --prep_def_merge_prop_impl              false
% 3.51/0.98  --prep_def_merge_mbd                    true
% 3.51/0.98  --prep_def_merge_tr_red                 false
% 3.51/0.98  --prep_def_merge_tr_cl                  false
% 3.51/0.98  --smt_preprocessing                     true
% 3.51/0.98  --smt_ac_axioms                         fast
% 3.51/0.98  --preprocessed_out                      false
% 3.51/0.98  --preprocessed_stats                    false
% 3.51/0.98  
% 3.51/0.98  ------ Abstraction refinement Options
% 3.51/0.98  
% 3.51/0.98  --abstr_ref                             []
% 3.51/0.98  --abstr_ref_prep                        false
% 3.51/0.98  --abstr_ref_until_sat                   false
% 3.51/0.98  --abstr_ref_sig_restrict                funpre
% 3.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.98  --abstr_ref_under                       []
% 3.51/0.98  
% 3.51/0.98  ------ SAT Options
% 3.51/0.98  
% 3.51/0.98  --sat_mode                              false
% 3.51/0.98  --sat_fm_restart_options                ""
% 3.51/0.98  --sat_gr_def                            false
% 3.51/0.98  --sat_epr_types                         true
% 3.51/0.98  --sat_non_cyclic_types                  false
% 3.51/0.98  --sat_finite_models                     false
% 3.51/0.98  --sat_fm_lemmas                         false
% 3.51/0.98  --sat_fm_prep                           false
% 3.51/0.98  --sat_fm_uc_incr                        true
% 3.51/0.98  --sat_out_model                         small
% 3.51/0.98  --sat_out_clauses                       false
% 3.51/0.98  
% 3.51/0.98  ------ QBF Options
% 3.51/0.98  
% 3.51/0.98  --qbf_mode                              false
% 3.51/0.98  --qbf_elim_univ                         false
% 3.51/0.98  --qbf_dom_inst                          none
% 3.51/0.98  --qbf_dom_pre_inst                      false
% 3.51/0.98  --qbf_sk_in                             false
% 3.51/0.98  --qbf_pred_elim                         true
% 3.51/0.98  --qbf_split                             512
% 3.51/0.98  
% 3.51/0.98  ------ BMC1 Options
% 3.51/0.98  
% 3.51/0.98  --bmc1_incremental                      false
% 3.51/0.98  --bmc1_axioms                           reachable_all
% 3.51/0.98  --bmc1_min_bound                        0
% 3.51/0.98  --bmc1_max_bound                        -1
% 3.51/0.98  --bmc1_max_bound_default                -1
% 3.51/0.98  --bmc1_symbol_reachability              true
% 3.51/0.98  --bmc1_property_lemmas                  false
% 3.51/0.98  --bmc1_k_induction                      false
% 3.51/0.98  --bmc1_non_equiv_states                 false
% 3.51/0.98  --bmc1_deadlock                         false
% 3.51/0.98  --bmc1_ucm                              false
% 3.51/0.98  --bmc1_add_unsat_core                   none
% 3.51/0.98  --bmc1_unsat_core_children              false
% 3.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.98  --bmc1_out_stat                         full
% 3.51/0.98  --bmc1_ground_init                      false
% 3.51/0.98  --bmc1_pre_inst_next_state              false
% 3.51/0.98  --bmc1_pre_inst_state                   false
% 3.51/0.98  --bmc1_pre_inst_reach_state             false
% 3.51/0.98  --bmc1_out_unsat_core                   false
% 3.51/0.98  --bmc1_aig_witness_out                  false
% 3.51/0.98  --bmc1_verbose                          false
% 3.51/0.98  --bmc1_dump_clauses_tptp                false
% 3.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.98  --bmc1_dump_file                        -
% 3.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.98  --bmc1_ucm_extend_mode                  1
% 3.51/0.98  --bmc1_ucm_init_mode                    2
% 3.51/0.98  --bmc1_ucm_cone_mode                    none
% 3.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.98  --bmc1_ucm_relax_model                  4
% 3.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.98  --bmc1_ucm_layered_model                none
% 3.51/0.98  --bmc1_ucm_max_lemma_size               10
% 3.51/0.98  
% 3.51/0.98  ------ AIG Options
% 3.51/0.98  
% 3.51/0.98  --aig_mode                              false
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation Options
% 3.51/0.98  
% 3.51/0.98  --instantiation_flag                    true
% 3.51/0.98  --inst_sos_flag                         false
% 3.51/0.98  --inst_sos_phase                        true
% 3.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel_side                     none
% 3.51/0.98  --inst_solver_per_active                1400
% 3.51/0.98  --inst_solver_calls_frac                1.
% 3.51/0.98  --inst_passive_queue_type               priority_queues
% 3.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.98  --inst_passive_queues_freq              [25;2]
% 3.51/0.98  --inst_dismatching                      true
% 3.51/0.98  --inst_eager_unprocessed_to_passive     true
% 3.51/0.98  --inst_prop_sim_given                   true
% 3.51/0.98  --inst_prop_sim_new                     false
% 3.51/0.98  --inst_subs_new                         false
% 3.51/0.98  --inst_eq_res_simp                      false
% 3.51/0.98  --inst_subs_given                       false
% 3.51/0.98  --inst_orphan_elimination               true
% 3.51/0.98  --inst_learning_loop_flag               true
% 3.51/0.98  --inst_learning_start                   3000
% 3.51/0.98  --inst_learning_factor                  2
% 3.51/0.98  --inst_start_prop_sim_after_learn       3
% 3.51/0.98  --inst_sel_renew                        solver
% 3.51/0.98  --inst_lit_activity_flag                true
% 3.51/0.98  --inst_restr_to_given                   false
% 3.51/0.98  --inst_activity_threshold               500
% 3.51/0.98  --inst_out_proof                        true
% 3.51/0.98  
% 3.51/0.98  ------ Resolution Options
% 3.51/0.98  
% 3.51/0.98  --resolution_flag                       false
% 3.51/0.98  --res_lit_sel                           adaptive
% 3.51/0.98  --res_lit_sel_side                      none
% 3.51/0.98  --res_ordering                          kbo
% 3.51/0.98  --res_to_prop_solver                    active
% 3.51/0.98  --res_prop_simpl_new                    false
% 3.51/0.98  --res_prop_simpl_given                  true
% 3.51/0.98  --res_passive_queue_type                priority_queues
% 3.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.98  --res_passive_queues_freq               [15;5]
% 3.51/0.98  --res_forward_subs                      full
% 3.51/0.98  --res_backward_subs                     full
% 3.51/0.98  --res_forward_subs_resolution           true
% 3.51/0.98  --res_backward_subs_resolution          true
% 3.51/0.98  --res_orphan_elimination                true
% 3.51/0.98  --res_time_limit                        2.
% 3.51/0.98  --res_out_proof                         true
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Options
% 3.51/0.98  
% 3.51/0.98  --superposition_flag                    true
% 3.51/0.98  --sup_passive_queue_type                priority_queues
% 3.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.98  --demod_completeness_check              fast
% 3.51/0.98  --demod_use_ground                      true
% 3.51/0.98  --sup_to_prop_solver                    passive
% 3.51/0.98  --sup_prop_simpl_new                    true
% 3.51/0.98  --sup_prop_simpl_given                  true
% 3.51/0.98  --sup_fun_splitting                     false
% 3.51/0.98  --sup_smt_interval                      50000
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Simplification Setup
% 3.51/0.98  
% 3.51/0.98  --sup_indices_passive                   []
% 3.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.98  --sup_full_bw                           [BwDemod]
% 3.51/0.98  --sup_immed_triv                        [TrivRules]
% 3.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.98  --sup_immed_bw_main                     []
% 3.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.98  
% 3.51/0.98  ------ Combination Options
% 3.51/0.98  
% 3.51/0.98  --comb_res_mult                         3
% 3.51/0.98  --comb_sup_mult                         2
% 3.51/0.98  --comb_inst_mult                        10
% 3.51/0.98  
% 3.51/0.98  ------ Debug Options
% 3.51/0.98  
% 3.51/0.98  --dbg_backtrace                         false
% 3.51/0.98  --dbg_dump_prop_clauses                 false
% 3.51/0.98  --dbg_dump_prop_clauses_file            -
% 3.51/0.98  --dbg_out_stat                          false
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  ------ Proving...
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  % SZS status Theorem for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  fof(f13,conjecture,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f14,negated_conjecture,(
% 3.51/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 3.51/0.98    inference(negated_conjecture,[],[f13])).
% 3.51/0.98  
% 3.51/0.98  fof(f26,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f14])).
% 3.51/0.98  
% 3.51/0.98  fof(f27,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.51/0.98    inference(flattening,[],[f26])).
% 3.51/0.98  
% 3.51/0.98  fof(f47,plain,(
% 3.51/0.98    ( ! [X2,X1] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v3_pre_topc(sK9,X2) & sK9 = X1 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f46,plain,(
% 3.51/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v3_pre_topc(X3,sK8) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) & v3_pre_topc(X1,X0) & m1_pre_topc(sK8,X0))) )),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f45,plain,(
% 3.51/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK7,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f44,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f48,plain,(
% 3.51/0.98    (((~v3_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & v3_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6)),
% 3.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f27,f47,f46,f45,f44])).
% 3.51/0.98  
% 3.51/0.98  fof(f80,plain,(
% 3.51/0.98    m1_pre_topc(sK8,sK6)),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f11,axiom,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f24,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f11])).
% 3.51/0.98  
% 3.51/0.98  fof(f73,plain,(
% 3.51/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f24])).
% 3.51/0.98  
% 3.51/0.98  fof(f78,plain,(
% 3.51/0.98    l1_pre_topc(sK6)),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f10,axiom,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f23,plain,(
% 3.51/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f10])).
% 3.51/0.98  
% 3.51/0.98  fof(f72,plain,(
% 3.51/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f23])).
% 3.51/0.98  
% 3.51/0.98  fof(f7,axiom,(
% 3.51/0.98    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f19,plain,(
% 3.51/0.98    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f7])).
% 3.51/0.98  
% 3.51/0.98  fof(f56,plain,(
% 3.51/0.98    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f19])).
% 3.51/0.98  
% 3.51/0.98  fof(f82,plain,(
% 3.51/0.98    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f6,axiom,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f17,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f6])).
% 3.51/0.98  
% 3.51/0.98  fof(f18,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(flattening,[],[f17])).
% 3.51/0.98  
% 3.51/0.98  fof(f31,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(nnf_transformation,[],[f18])).
% 3.51/0.98  
% 3.51/0.98  fof(f54,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f31])).
% 3.51/0.98  
% 3.51/0.98  fof(f90,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(equality_resolution,[],[f54])).
% 3.51/0.98  
% 3.51/0.98  fof(f9,axiom,(
% 3.51/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f21,plain,(
% 3.51/0.98    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f9])).
% 3.51/0.98  
% 3.51/0.98  fof(f22,plain,(
% 3.51/0.98    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(flattening,[],[f21])).
% 3.51/0.98  
% 3.51/0.98  fof(f71,plain,(
% 3.51/0.98    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f22])).
% 3.51/0.98  
% 3.51/0.98  fof(f70,plain,(
% 3.51/0.98    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f22])).
% 3.51/0.98  
% 3.51/0.98  fof(f8,axiom,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f20,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f8])).
% 3.51/0.98  
% 3.51/0.98  fof(f29,plain,(
% 3.51/0.98    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 3.51/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.51/0.98  
% 3.51/0.98  fof(f28,plain,(
% 3.51/0.98    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 3.51/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.51/0.98  
% 3.51/0.98  fof(f30,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(definition_folding,[],[f20,f29,f28])).
% 3.51/0.98  
% 3.51/0.98  fof(f69,plain,(
% 3.51/0.98    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f30])).
% 3.51/0.98  
% 3.51/0.98  fof(f32,plain,(
% 3.51/0.98    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 3.51/0.98    inference(nnf_transformation,[],[f29])).
% 3.51/0.98  
% 3.51/0.98  fof(f57,plain,(
% 3.51/0.98    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f32])).
% 3.51/0.98  
% 3.51/0.98  fof(f1,axiom,(
% 3.51/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f15,plain,(
% 3.51/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.51/0.98    inference(ennf_transformation,[],[f1])).
% 3.51/0.98  
% 3.51/0.98  fof(f49,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f15])).
% 3.51/0.98  
% 3.51/0.98  fof(f5,axiom,(
% 3.51/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f53,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f5])).
% 3.51/0.98  
% 3.51/0.98  fof(f85,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.51/0.98    inference(definition_unfolding,[],[f49,f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f33,plain,(
% 3.51/0.98    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.51/0.98    inference(nnf_transformation,[],[f28])).
% 3.51/0.98  
% 3.51/0.98  fof(f34,plain,(
% 3.51/0.98    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 3.51/0.98    inference(flattening,[],[f33])).
% 3.51/0.98  
% 3.51/0.98  fof(f35,plain,(
% 3.51/0.98    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.51/0.98    inference(rectify,[],[f34])).
% 3.51/0.98  
% 3.51/0.98  fof(f38,plain,(
% 3.51/0.98    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f37,plain,(
% 3.51/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f36,plain,(
% 3.51/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f39,plain,(
% 3.51/0.98    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 3.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f38,f37,f36])).
% 3.51/0.98  
% 3.51/0.98  fof(f59,plain,(
% 3.51/0.98    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f39])).
% 3.51/0.98  
% 3.51/0.98  fof(f12,axiom,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f25,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f12])).
% 3.51/0.98  
% 3.51/0.98  fof(f40,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(nnf_transformation,[],[f25])).
% 3.51/0.98  
% 3.51/0.98  fof(f41,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(rectify,[],[f40])).
% 3.51/0.98  
% 3.51/0.98  fof(f42,plain,(
% 3.51/0.98    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f43,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 3.51/0.98  
% 3.51/0.98  fof(f77,plain,(
% 3.51/0.98    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f43])).
% 3.51/0.98  
% 3.51/0.98  fof(f92,plain,(
% 3.51/0.98    ( ! [X0,X3,X1] : (v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(equality_resolution,[],[f77])).
% 3.51/0.98  
% 3.51/0.98  fof(f3,axiom,(
% 3.51/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f51,plain,(
% 3.51/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f3])).
% 3.51/0.98  
% 3.51/0.98  fof(f2,axiom,(
% 3.51/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f50,plain,(
% 3.51/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.51/0.98    inference(cnf_transformation,[],[f2])).
% 3.51/0.98  
% 3.51/0.98  fof(f4,axiom,(
% 3.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f16,plain,(
% 3.51/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f4])).
% 3.51/0.98  
% 3.51/0.98  fof(f52,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f16])).
% 3.51/0.98  
% 3.51/0.98  fof(f86,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(definition_unfolding,[],[f52,f53])).
% 3.51/0.98  
% 3.51/0.98  fof(f84,plain,(
% 3.51/0.98    ~v3_pre_topc(sK9,sK8)),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f81,plain,(
% 3.51/0.98    v3_pre_topc(sK7,sK6)),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f83,plain,(
% 3.51/0.98    sK7 = sK9),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f87,plain,(
% 3.51/0.98    v3_pre_topc(sK9,sK6)),
% 3.51/0.98    inference(definition_unfolding,[],[f81,f83])).
% 3.51/0.98  
% 3.51/0.98  fof(f79,plain,(
% 3.51/0.98    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.51/0.98    inference(cnf_transformation,[],[f48])).
% 3.51/0.98  
% 3.51/0.98  fof(f88,plain,(
% 3.51/0.98    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.51/0.98    inference(definition_unfolding,[],[f79,f83])).
% 3.51/0.98  
% 3.51/0.98  cnf(c_31,negated_conjecture,
% 3.51/0.98      ( m1_pre_topc(sK8,sK6) ),
% 3.51/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2307,plain,
% 3.51/0.98      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_23,plain,
% 3.51/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2315,plain,
% 3.51/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/0.98      | l1_pre_topc(X1) != iProver_top
% 3.51/0.98      | l1_pre_topc(X0) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2696,plain,
% 3.51/0.98      ( l1_pre_topc(sK6) != iProver_top
% 3.51/0.98      | l1_pre_topc(sK8) = iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_2307,c_2315]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_33,negated_conjecture,
% 3.51/0.98      ( l1_pre_topc(sK6) ),
% 3.51/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_34,plain,
% 3.51/0.98      ( l1_pre_topc(sK6) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_716,plain,
% 3.51/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X0 | sK8 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_717,plain,
% 3.51/0.98      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_716]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_718,plain,
% 3.51/0.98      ( l1_pre_topc(sK6) != iProver_top
% 3.51/0.98      | l1_pre_topc(sK8) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2927,plain,
% 3.51/0.98      ( l1_pre_topc(sK8) = iProver_top ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_2696,c_34,c_718]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_22,plain,
% 3.51/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6,plain,
% 3.51/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_384,plain,
% 3.51/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_22,c_6]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2303,plain,
% 3.51/0.98      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.51/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3387,plain,
% 3.51/0.98      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_2927,c_2303]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_29,negated_conjecture,
% 3.51/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.51/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2309,plain,
% 3.51/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3879,plain,
% 3.51/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) = iProver_top ),
% 3.51/0.98      inference(demodulation,[status(thm)],[c_3387,c_2309]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5,plain,
% 3.51/0.98      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 3.51/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.98      | ~ l1_pre_topc(X0)
% 3.51/0.98      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 3.51/0.98      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 3.51/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_20,plain,
% 3.51/0.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 3.51/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.98      | ~ l1_pre_topc(X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_215,plain,
% 3.51/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.98      | ~ l1_pre_topc(X0)
% 3.51/0.98      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 3.51/0.98      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_5,c_20]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_216,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1)
% 3.51/0.98      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 3.51/0.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.51/0.98      inference(renaming,[status(thm)],[c_215]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_21,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1)
% 3.51/0.98      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 3.51/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_221,plain,
% 3.51/0.98      ( ~ l1_pre_topc(X1)
% 3.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_216,c_21]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_222,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1)
% 3.51/0.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.51/0.98      inference(renaming,[status(thm)],[c_221]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2304,plain,
% 3.51/0.98      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 3.51/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_4194,plain,
% 3.51/0.98      ( k2_struct_0(k1_pre_topc(sK8,X0)) = X0
% 3.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 3.51/0.98      | l1_pre_topc(sK8) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_3387,c_2304]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_7421,plain,
% 3.51/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 3.51/0.98      | k2_struct_0(k1_pre_topc(sK8,X0)) = X0 ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_4194,c_34,c_718]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_7422,plain,
% 3.51/0.98      ( k2_struct_0(k1_pre_topc(sK8,X0)) = X0
% 3.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top ),
% 3.51/0.98      inference(renaming,[status(thm)],[c_7421]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_7430,plain,
% 3.51/0.98      ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_3879,c_7422]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2317,plain,
% 3.51/0.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 3.51/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2906,plain,
% 3.51/0.98      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 3.51/0.98      | l1_pre_topc(sK8) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_2309,c_2317]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_38,plain,
% 3.51/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2495,plain,
% 3.51/0.98      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
% 3.51/0.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.51/0.98      | ~ l1_pre_topc(sK8) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2496,plain,
% 3.51/0.98      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 3.51/0.98      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 3.51/0.98      | l1_pre_topc(sK8) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_2495]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3244,plain,
% 3.51/0.98      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_2906,c_34,c_38,c_718,c_2496]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_19,plain,
% 3.51/0.98      ( sP1(X0,X1) | ~ l1_pre_topc(X0) | ~ l1_pre_topc(X1) ),
% 3.51/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_8,plain,
% 3.51/0.98      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_428,plain,
% 3.51/0.98      ( sP0(X0,X1)
% 3.51/0.98      | ~ m1_pre_topc(X0,X1)
% 3.51/0.98      | ~ l1_pre_topc(X0)
% 3.51/0.98      | ~ l1_pre_topc(X1) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_19,c_8]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_432,plain,
% 3.51/0.98      ( ~ m1_pre_topc(X0,X1) | sP0(X0,X1) | ~ l1_pre_topc(X1) ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_428,c_23]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_433,plain,
% 3.51/0.98      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 3.51/0.98      inference(renaming,[status(thm)],[c_432]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_0,plain,
% 3.51/0.98      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 3.51/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_18,plain,
% 3.51/0.98      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 3.51/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_476,plain,
% 3.51/0.98      ( ~ sP0(X0,X1)
% 3.51/0.98      | k2_struct_0(X1) != X2
% 3.51/0.98      | k2_struct_0(X0) != X3
% 3.51/0.98      | k1_setfam_1(k2_tarski(X3,X2)) = X3 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_477,plain,
% 3.51/0.98      ( ~ sP0(X0,X1)
% 3.51/0.98      | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_476]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1196,plain,
% 3.51/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.98      | ~ l1_pre_topc(X1)
% 3.51/0.98      | k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0) ),
% 3.51/0.98      inference(resolution,[status(thm)],[c_433,c_477]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2302,plain,
% 3.51/0.98      ( k1_setfam_1(k2_tarski(k2_struct_0(X0),k2_struct_0(X1))) = k2_struct_0(X0)
% 3.51/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 3.51/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_1196]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3250,plain,
% 3.51/0.98      ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9))
% 3.51/0.98      | l1_pre_topc(sK8) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_3244,c_2302]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2586,plain,
% 3.51/0.98      ( ~ m1_pre_topc(k1_pre_topc(sK8,sK9),sK8)
% 3.51/0.98      | ~ l1_pre_topc(sK8)
% 3.51/0.98      | k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_4469,plain,
% 3.51/0.98      ( k1_setfam_1(k2_tarski(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8))) = k2_struct_0(k1_pre_topc(sK8,sK9)) ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_3250,c_33,c_29,c_717,c_2495,c_2586]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_7513,plain,
% 3.51/0.98      ( k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))) = sK9 ),
% 3.51/0.98      inference(demodulation,[status(thm)],[c_7430,c_4469]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_24,plain,
% 3.51/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.51/0.98      | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 3.51/0.98      | ~ m1_pre_topc(X2,X1)
% 3.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 3.51/0.98      | ~ l1_pre_topc(X1) ),
% 3.51/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2314,plain,
% 3.51/0.98      ( v3_pre_topc(X0,X1) != iProver_top
% 3.51/0.98      | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2) = iProver_top
% 3.51/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.51/0.98      | m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.51/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_4243,plain,
% 3.51/0.98      ( v3_pre_topc(X0,X1) != iProver_top
% 3.51/0.98      | v3_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
% 3.51/0.98      | m1_pre_topc(sK8,X1) != iProver_top
% 3.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.51/0.98      | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 3.51/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_3387,c_2314]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_4264,plain,
% 3.51/0.98      ( v3_pre_topc(X0,X1) != iProver_top
% 3.51/0.98      | v3_pre_topc(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),sK8) = iProver_top
% 3.51/0.98      | m1_pre_topc(sK8,X1) != iProver_top
% 3.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.51/0.98      | m1_subset_1(k9_subset_1(k2_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 3.51/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.51/0.98      inference(light_normalisation,[status(thm)],[c_4243,c_3387]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2,plain,
% 3.51/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.51/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2320,plain,
% 3.51/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1,plain,
% 3.51/0.98      ( k2_subset_1(X0) = X0 ),
% 3.51/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2335,plain,
% 3.51/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.51/0.98      inference(light_normalisation,[status(thm)],[c_2320,c_1]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.51/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2319,plain,
% 3.51/0.98      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.51/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2767,plain,
% 3.51/0.98      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_2335,c_2319]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10451,plain,
% 3.51/0.98      ( v3_pre_topc(X0,X1) != iProver_top
% 3.51/0.98      | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),sK8) = iProver_top
% 3.51/0.98      | m1_pre_topc(sK8,X1) != iProver_top
% 3.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.51/0.98      | m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK8))),k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 3.51/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.51/0.98      inference(demodulation,[status(thm)],[c_4264,c_2767]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10461,plain,
% 3.51/0.98      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK9,k2_struct_0(sK8))),sK8) = iProver_top
% 3.51/0.98      | v3_pre_topc(sK9,X0) != iProver_top
% 3.51/0.98      | m1_pre_topc(sK8,X0) != iProver_top
% 3.51/0.98      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 3.51/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_7513,c_10451]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10462,plain,
% 3.51/0.98      ( v3_pre_topc(sK9,X0) != iProver_top
% 3.51/0.98      | v3_pre_topc(sK9,sK8) = iProver_top
% 3.51/0.98      | m1_pre_topc(sK8,X0) != iProver_top
% 3.51/0.98      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 3.51/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.98      inference(light_normalisation,[status(thm)],[c_10461,c_7513]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10464,plain,
% 3.51/0.98      ( v3_pre_topc(sK9,sK6) != iProver_top
% 3.51/0.98      | v3_pre_topc(sK9,sK8) = iProver_top
% 3.51/0.98      | m1_pre_topc(sK8,sK6) != iProver_top
% 3.51/0.98      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.51/0.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_struct_0(sK8))) != iProver_top
% 3.51/0.98      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_10462]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_28,negated_conjecture,
% 3.51/0.98      ( ~ v3_pre_topc(sK9,sK8) ),
% 3.51/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_39,plain,
% 3.51/0.98      ( v3_pre_topc(sK9,sK8) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_30,negated_conjecture,
% 3.51/0.98      ( v3_pre_topc(sK9,sK6) ),
% 3.51/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_37,plain,
% 3.51/0.98      ( v3_pre_topc(sK9,sK6) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_36,plain,
% 3.51/0.98      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_32,negated_conjecture,
% 3.51/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.51/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_35,plain,
% 3.51/0.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(contradiction,plain,
% 3.51/0.98      ( $false ),
% 3.51/0.98      inference(minisat,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_10464,c_3879,c_39,c_37,c_36,c_35,c_34]) ).
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  ------                               Statistics
% 3.51/0.98  
% 3.51/0.98  ------ General
% 3.51/0.98  
% 3.51/0.98  abstr_ref_over_cycles:                  0
% 3.51/0.98  abstr_ref_under_cycles:                 0
% 3.51/0.98  gc_basic_clause_elim:                   0
% 3.51/0.98  forced_gc_time:                         0
% 3.51/0.98  parsing_time:                           0.01
% 3.51/0.98  unif_index_cands_time:                  0.
% 3.51/0.98  unif_index_add_time:                    0.
% 3.51/0.98  orderings_time:                         0.
% 3.51/0.98  out_proof_time:                         0.01
% 3.51/0.98  total_time:                             0.311
% 3.51/0.98  num_of_symbols:                         57
% 3.51/0.98  num_of_terms:                           9336
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing
% 3.51/0.98  
% 3.51/0.98  num_of_splits:                          0
% 3.51/0.98  num_of_split_atoms:                     0
% 3.51/0.98  num_of_reused_defs:                     0
% 3.51/0.98  num_eq_ax_congr_red:                    43
% 3.51/0.98  num_of_sem_filtered_clauses:            6
% 3.51/0.98  num_of_subtypes:                        0
% 3.51/0.98  monotx_restored_types:                  0
% 3.51/0.98  sat_num_of_epr_types:                   0
% 3.51/0.98  sat_num_of_non_cyclic_types:            0
% 3.51/0.98  sat_guarded_non_collapsed_types:        0
% 3.51/0.98  num_pure_diseq_elim:                    0
% 3.51/0.98  simp_replaced_by:                       0
% 3.51/0.98  res_preprocessed:                       150
% 3.51/0.98  prep_upred:                             0
% 3.51/0.98  prep_unflattend:                        97
% 3.51/0.98  smt_new_axioms:                         0
% 3.51/0.98  pred_elim_cands:                        5
% 3.51/0.98  pred_elim:                              4
% 3.51/0.98  pred_elim_cl:                           9
% 3.51/0.98  pred_elim_cycles:                       10
% 3.51/0.98  merged_defs:                            0
% 3.51/0.98  merged_defs_ncl:                        0
% 3.51/0.98  bin_hyper_res:                          0
% 3.51/0.98  prep_cycles:                            5
% 3.51/0.98  pred_elim_time:                         0.025
% 3.51/0.98  splitting_time:                         0.
% 3.51/0.98  sem_filter_time:                        0.
% 3.51/0.98  monotx_time:                            0.
% 3.51/0.98  subtype_inf_time:                       0.
% 3.51/0.98  
% 3.51/0.98  ------ Problem properties
% 3.51/0.98  
% 3.51/0.98  clauses:                                20
% 3.51/0.98  conjectures:                            6
% 3.51/0.98  epr:                                    5
% 3.51/0.98  horn:                                   20
% 3.51/0.98  ground:                                 6
% 3.51/0.98  unary:                                  8
% 3.51/0.98  binary:                                 2
% 3.51/0.98  lits:                                   53
% 3.51/0.98  lits_eq:                                7
% 3.51/0.98  fd_pure:                                0
% 3.51/0.98  fd_pseudo:                              0
% 3.51/0.98  fd_cond:                                0
% 3.51/0.98  fd_pseudo_cond:                         0
% 3.51/0.98  ac_symbols:                             0
% 3.51/0.98  
% 3.51/0.98  ------ Propositional Solver
% 3.51/0.98  
% 3.51/0.98  prop_solver_calls:                      31
% 3.51/0.98  prop_fast_solver_calls:                 1642
% 3.51/0.98  smt_solver_calls:                       0
% 3.51/0.98  smt_fast_solver_calls:                  0
% 3.51/0.98  prop_num_of_clauses:                    3934
% 3.51/0.98  prop_preprocess_simplified:             9211
% 3.51/0.98  prop_fo_subsumed:                       75
% 3.51/0.98  prop_solver_time:                       0.
% 3.51/0.98  smt_solver_time:                        0.
% 3.51/0.98  smt_fast_solver_time:                   0.
% 3.51/0.98  prop_fast_solver_time:                  0.
% 3.51/0.98  prop_unsat_core_time:                   0.
% 3.51/0.98  
% 3.51/0.98  ------ QBF
% 3.51/0.98  
% 3.51/0.98  qbf_q_res:                              0
% 3.51/0.98  qbf_num_tautologies:                    0
% 3.51/0.98  qbf_prep_cycles:                        0
% 3.51/0.98  
% 3.51/0.98  ------ BMC1
% 3.51/0.98  
% 3.51/0.98  bmc1_current_bound:                     -1
% 3.51/0.98  bmc1_last_solved_bound:                 -1
% 3.51/0.98  bmc1_unsat_core_size:                   -1
% 3.51/0.98  bmc1_unsat_core_parents_size:           -1
% 3.51/0.98  bmc1_merge_next_fun:                    0
% 3.51/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation
% 3.51/0.98  
% 3.51/0.98  inst_num_of_clauses:                    1152
% 3.51/0.98  inst_num_in_passive:                    56
% 3.51/0.98  inst_num_in_active:                     571
% 3.51/0.98  inst_num_in_unprocessed:                526
% 3.51/0.98  inst_num_of_loops:                      590
% 3.51/0.98  inst_num_of_learning_restarts:          0
% 3.51/0.98  inst_num_moves_active_passive:          16
% 3.51/0.98  inst_lit_activity:                      0
% 3.51/0.98  inst_lit_activity_moves:                0
% 3.51/0.98  inst_num_tautologies:                   0
% 3.51/0.98  inst_num_prop_implied:                  0
% 3.51/0.98  inst_num_existing_simplified:           0
% 3.51/0.98  inst_num_eq_res_simplified:             0
% 3.51/0.98  inst_num_child_elim:                    0
% 3.51/0.98  inst_num_of_dismatching_blockings:      311
% 3.51/0.98  inst_num_of_non_proper_insts:           993
% 3.51/0.98  inst_num_of_duplicates:                 0
% 3.51/0.98  inst_inst_num_from_inst_to_res:         0
% 3.51/0.98  inst_dismatching_checking_time:         0.
% 3.51/0.98  
% 3.51/0.98  ------ Resolution
% 3.51/0.98  
% 3.51/0.98  res_num_of_clauses:                     0
% 3.51/0.98  res_num_in_passive:                     0
% 3.51/0.98  res_num_in_active:                      0
% 3.51/0.98  res_num_of_loops:                       155
% 3.51/0.98  res_forward_subset_subsumed:            55
% 3.51/0.98  res_backward_subset_subsumed:           4
% 3.51/0.98  res_forward_subsumed:                   0
% 3.51/0.98  res_backward_subsumed:                  0
% 3.51/0.98  res_forward_subsumption_resolution:     0
% 3.51/0.98  res_backward_subsumption_resolution:    0
% 3.51/0.98  res_clause_to_clause_subsumption:       515
% 3.51/0.98  res_orphan_elimination:                 0
% 3.51/0.98  res_tautology_del:                      72
% 3.51/0.98  res_num_eq_res_simplified:              0
% 3.51/0.98  res_num_sel_changes:                    0
% 3.51/0.98  res_moves_from_active_to_pass:          0
% 3.51/0.98  
% 3.51/0.98  ------ Superposition
% 3.51/0.98  
% 3.51/0.98  sup_time_total:                         0.
% 3.51/0.98  sup_time_generating:                    0.
% 3.51/0.98  sup_time_sim_full:                      0.
% 3.51/0.98  sup_time_sim_immed:                     0.
% 3.51/0.98  
% 3.51/0.98  sup_num_of_clauses:                     194
% 3.51/0.98  sup_num_in_active:                      109
% 3.51/0.98  sup_num_in_passive:                     85
% 3.51/0.98  sup_num_of_loops:                       116
% 3.51/0.98  sup_fw_superposition:                   116
% 3.51/0.98  sup_bw_superposition:                   98
% 3.51/0.98  sup_immediate_simplified:               61
% 3.51/0.98  sup_given_eliminated:                   0
% 3.51/0.98  comparisons_done:                       0
% 3.51/0.98  comparisons_avoided:                    0
% 3.51/0.98  
% 3.51/0.98  ------ Simplifications
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  sim_fw_subset_subsumed:                 6
% 3.51/0.98  sim_bw_subset_subsumed:                 0
% 3.51/0.98  sim_fw_subsumed:                        4
% 3.51/0.98  sim_bw_subsumed:                        0
% 3.51/0.98  sim_fw_subsumption_res:                 0
% 3.51/0.98  sim_bw_subsumption_res:                 0
% 3.51/0.98  sim_tautology_del:                      0
% 3.51/0.98  sim_eq_tautology_del:                   7
% 3.51/0.98  sim_eq_res_simp:                        0
% 3.51/0.98  sim_fw_demodulated:                     14
% 3.51/0.98  sim_bw_demodulated:                     8
% 3.51/0.98  sim_light_normalised:                   59
% 3.51/0.98  sim_joinable_taut:                      0
% 3.51/0.98  sim_joinable_simp:                      0
% 3.51/0.98  sim_ac_normalised:                      0
% 3.51/0.98  sim_smt_subsumption:                    0
% 3.51/0.98  
%------------------------------------------------------------------------------
