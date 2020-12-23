%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:44 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 686 expanded)
%              Number of clauses        :   78 ( 220 expanded)
%              Number of leaves         :   20 ( 208 expanded)
%              Depth                    :   21
%              Number of atoms          :  573 (3730 expanded)
%              Number of equality atoms :  170 ( 775 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v4_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v4_pre_topc(sK9,X2)
        & sK9 = X1
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f44,plain,
    ( ~ v4_pre_topc(sK9,sK8)
    & sK7 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v4_pre_topc(sK7,sK6)
    & m1_pre_topc(sK8,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f23,f43,f42,f41,f40])).

fof(f75,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f25,f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f24])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f72,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ~ v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1906,plain,
    ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1893,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2296,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_19,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1902,plain,
    ( m1_pre_topc(k1_pre_topc(X0_52,X0_53),X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2288,plain,
    ( m1_pre_topc(k1_pre_topc(X0_52,X0_53),X0_52) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1902])).

cnf(c_2766,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_2288])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_679,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_680,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_681,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_2990,plain,
    ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2766,c_33,c_681])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ m1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_391,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_18,c_7])).

cnf(c_395,plain,
    ( ~ m1_pre_topc(X0,X1)
    | sP0(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_21])).

cnf(c_396,plain,
    ( sP0(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_439,plain,
    ( ~ sP0(X0,X1)
    | k3_xboole_0(X2,X3) = X2
    | k2_struct_0(X1) != X3
    | k2_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_440,plain,
    ( ~ sP0(X0,X1)
    | k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_1152,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_396,c_440])).

cnf(c_1887,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | k3_xboole_0(k2_struct_0(X0_52),k2_struct_0(X1_52)) = k2_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_1152])).

cnf(c_2302,plain,
    ( k3_xboole_0(k2_struct_0(X0_52),k2_struct_0(X1_52)) = k2_struct_0(X0_52)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1887])).

cnf(c_4227,plain,
    ( k3_xboole_0(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8)) = k2_struct_0(k1_pre_topc(sK8,sK9))
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2990,c_2302])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_19])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_208,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_203,c_20])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_1888,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ l1_pre_topc(X0_52)
    | k2_struct_0(k1_pre_topc(X0_52,X0_53)) = X0_53 ),
    inference(subtyping,[status(esa)],[c_209])).

cnf(c_2301,plain,
    ( k2_struct_0(k1_pre_topc(X0_52,X0_53)) = X0_53
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1888])).

cnf(c_3700,plain,
    ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9
    | l1_pre_topc(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_2301])).

cnf(c_3727,plain,
    ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3700,c_33,c_681])).

cnf(c_4247,plain,
    ( k3_xboole_0(sK9,k2_struct_0(sK8)) = sK9
    | l1_pre_topc(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4227,c_3727])).

cnf(c_4674,plain,
    ( k3_xboole_0(sK9,k2_struct_0(sK8)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4247,c_33,c_681])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1905,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X0_55))
    | k9_subset_1(X0_55,X0_53,X1_53) = k9_subset_1(X0_55,X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2285,plain,
    ( k9_subset_1(X0_55,X0_53,X1_53) = k9_subset_1(X0_55,X1_53,X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1905])).

cnf(c_2620,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,X0_53) = k9_subset_1(u1_struct_0(sK8),X0_53,sK9) ),
    inference(superposition,[status(thm)],[c_2296,c_2285])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1904,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X0_55))
    | k9_subset_1(X0_55,X1_53,X0_53) = k3_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2286,plain,
    ( k9_subset_1(X0_55,X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1904])).

cnf(c_2631,plain,
    ( k9_subset_1(u1_struct_0(sK8),X0_53,sK9) = k3_xboole_0(X0_53,sK9) ),
    inference(superposition,[status(thm)],[c_2296,c_2286])).

cnf(c_2882,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,X0_53) = k3_xboole_0(X0_53,sK9) ),
    inference(light_normalisation,[status(thm)],[c_2620,c_2631])).

cnf(c_22,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1899,plain,
    ( ~ v4_pre_topc(X0_53,X0_52)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1_52),X0_53,k2_struct_0(X1_52)),X1_52)
    | ~ m1_pre_topc(X1_52,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1_52),X0_53,k2_struct_0(X1_52)),k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2291,plain,
    ( v4_pre_topc(X0_53,X0_52) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1_52),X0_53,k2_struct_0(X1_52)),X1_52) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(X1_52),X0_53,k2_struct_0(X1_52)),k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_3246,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
    | v4_pre_topc(sK9,X0_52) != iProver_top
    | m1_pre_topc(sK8,X0_52) != iProver_top
    | m1_subset_1(k3_xboole_0(k2_struct_0(sK8),sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2882,c_2291])).

cnf(c_3267,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
    | v4_pre_topc(sK9,X0_52) != iProver_top
    | m1_pre_topc(sK8,X0_52) != iProver_top
    | m1_subset_1(k3_xboole_0(k2_struct_0(sK8),sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3246,c_2882])).

cnf(c_35,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1890,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2299,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1890])).

cnf(c_27,negated_conjecture,
    ( sK7 = sK9 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1894,negated_conjecture,
    ( sK7 = sK9 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2318,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2299,c_1894])).

cnf(c_29,negated_conjecture,
    ( v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1892,negated_conjecture,
    ( v4_pre_topc(sK7,sK6) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2297,plain,
    ( v4_pre_topc(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_2307,plain,
    ( v4_pre_topc(sK9,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2297,c_1894])).

cnf(c_3278,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
    | v4_pre_topc(sK9,sK6) != iProver_top
    | m1_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(k3_xboole_0(k2_struct_0(sK8),sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3267])).

cnf(c_3500,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
    | m1_subset_1(k3_xboole_0(k2_struct_0(sK8),sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3267,c_33,c_35,c_2318,c_2307,c_3278])).

cnf(c_3506,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
    | m1_subset_1(k3_xboole_0(sK9,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_3500])).

cnf(c_4677,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4674,c_3506])).

cnf(c_37,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4781,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4677,c_37])).

cnf(c_4786,plain,
    ( v4_pre_topc(k3_xboole_0(sK9,k2_struct_0(sK8)),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_4781])).

cnf(c_4788,plain,
    ( v4_pre_topc(sK9,sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4786,c_4674])).

cnf(c_26,negated_conjecture,
    ( ~ v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_38,plain,
    ( v4_pre_topc(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4788,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.50/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/0.99  
% 2.50/0.99  ------  iProver source info
% 2.50/0.99  
% 2.50/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.50/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/0.99  git: non_committed_changes: false
% 2.50/0.99  git: last_make_outside_of_git: false
% 2.50/0.99  
% 2.50/0.99  ------ 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options
% 2.50/0.99  
% 2.50/0.99  --out_options                           all
% 2.50/0.99  --tptp_safe_out                         true
% 2.50/0.99  --problem_path                          ""
% 2.50/0.99  --include_path                          ""
% 2.50/0.99  --clausifier                            res/vclausify_rel
% 2.50/0.99  --clausifier_options                    --mode clausify
% 2.50/0.99  --stdin                                 false
% 2.50/0.99  --stats_out                             all
% 2.50/0.99  
% 2.50/0.99  ------ General Options
% 2.50/0.99  
% 2.50/0.99  --fof                                   false
% 2.50/0.99  --time_out_real                         305.
% 2.50/0.99  --time_out_virtual                      -1.
% 2.50/0.99  --symbol_type_check                     false
% 2.50/0.99  --clausify_out                          false
% 2.50/0.99  --sig_cnt_out                           false
% 2.50/0.99  --trig_cnt_out                          false
% 2.50/0.99  --trig_cnt_out_tolerance                1.
% 2.50/0.99  --trig_cnt_out_sk_spl                   false
% 2.50/0.99  --abstr_cl_out                          false
% 2.50/0.99  
% 2.50/0.99  ------ Global Options
% 2.50/0.99  
% 2.50/0.99  --schedule                              default
% 2.50/0.99  --add_important_lit                     false
% 2.50/0.99  --prop_solver_per_cl                    1000
% 2.50/0.99  --min_unsat_core                        false
% 2.50/0.99  --soft_assumptions                      false
% 2.50/0.99  --soft_lemma_size                       3
% 2.50/0.99  --prop_impl_unit_size                   0
% 2.50/0.99  --prop_impl_unit                        []
% 2.50/0.99  --share_sel_clauses                     true
% 2.50/0.99  --reset_solvers                         false
% 2.50/0.99  --bc_imp_inh                            [conj_cone]
% 2.50/0.99  --conj_cone_tolerance                   3.
% 2.50/0.99  --extra_neg_conj                        none
% 2.50/0.99  --large_theory_mode                     true
% 2.50/0.99  --prolific_symb_bound                   200
% 2.50/0.99  --lt_threshold                          2000
% 2.50/0.99  --clause_weak_htbl                      true
% 2.50/0.99  --gc_record_bc_elim                     false
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing Options
% 2.50/0.99  
% 2.50/0.99  --preprocessing_flag                    true
% 2.50/0.99  --time_out_prep_mult                    0.1
% 2.50/0.99  --splitting_mode                        input
% 2.50/0.99  --splitting_grd                         true
% 2.50/0.99  --splitting_cvd                         false
% 2.50/0.99  --splitting_cvd_svl                     false
% 2.50/0.99  --splitting_nvd                         32
% 2.50/0.99  --sub_typing                            true
% 2.50/0.99  --prep_gs_sim                           true
% 2.50/0.99  --prep_unflatten                        true
% 2.50/0.99  --prep_res_sim                          true
% 2.50/0.99  --prep_upred                            true
% 2.50/0.99  --prep_sem_filter                       exhaustive
% 2.50/0.99  --prep_sem_filter_out                   false
% 2.50/0.99  --pred_elim                             true
% 2.50/0.99  --res_sim_input                         true
% 2.50/0.99  --eq_ax_congr_red                       true
% 2.50/0.99  --pure_diseq_elim                       true
% 2.50/0.99  --brand_transform                       false
% 2.50/0.99  --non_eq_to_eq                          false
% 2.50/0.99  --prep_def_merge                        true
% 2.50/0.99  --prep_def_merge_prop_impl              false
% 2.50/0.99  --prep_def_merge_mbd                    true
% 2.50/0.99  --prep_def_merge_tr_red                 false
% 2.50/0.99  --prep_def_merge_tr_cl                  false
% 2.50/0.99  --smt_preprocessing                     true
% 2.50/0.99  --smt_ac_axioms                         fast
% 2.50/0.99  --preprocessed_out                      false
% 2.50/0.99  --preprocessed_stats                    false
% 2.50/0.99  
% 2.50/0.99  ------ Abstraction refinement Options
% 2.50/0.99  
% 2.50/0.99  --abstr_ref                             []
% 2.50/0.99  --abstr_ref_prep                        false
% 2.50/0.99  --abstr_ref_until_sat                   false
% 2.50/0.99  --abstr_ref_sig_restrict                funpre
% 2.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.99  --abstr_ref_under                       []
% 2.50/0.99  
% 2.50/0.99  ------ SAT Options
% 2.50/0.99  
% 2.50/0.99  --sat_mode                              false
% 2.50/0.99  --sat_fm_restart_options                ""
% 2.50/0.99  --sat_gr_def                            false
% 2.50/0.99  --sat_epr_types                         true
% 2.50/0.99  --sat_non_cyclic_types                  false
% 2.50/0.99  --sat_finite_models                     false
% 2.50/0.99  --sat_fm_lemmas                         false
% 2.50/0.99  --sat_fm_prep                           false
% 2.50/0.99  --sat_fm_uc_incr                        true
% 2.50/0.99  --sat_out_model                         small
% 2.50/0.99  --sat_out_clauses                       false
% 2.50/0.99  
% 2.50/0.99  ------ QBF Options
% 2.50/0.99  
% 2.50/0.99  --qbf_mode                              false
% 2.50/0.99  --qbf_elim_univ                         false
% 2.50/0.99  --qbf_dom_inst                          none
% 2.50/0.99  --qbf_dom_pre_inst                      false
% 2.50/0.99  --qbf_sk_in                             false
% 2.50/0.99  --qbf_pred_elim                         true
% 2.50/0.99  --qbf_split                             512
% 2.50/0.99  
% 2.50/0.99  ------ BMC1 Options
% 2.50/0.99  
% 2.50/0.99  --bmc1_incremental                      false
% 2.50/0.99  --bmc1_axioms                           reachable_all
% 2.50/0.99  --bmc1_min_bound                        0
% 2.50/0.99  --bmc1_max_bound                        -1
% 2.50/0.99  --bmc1_max_bound_default                -1
% 2.50/0.99  --bmc1_symbol_reachability              true
% 2.50/0.99  --bmc1_property_lemmas                  false
% 2.50/0.99  --bmc1_k_induction                      false
% 2.50/0.99  --bmc1_non_equiv_states                 false
% 2.50/0.99  --bmc1_deadlock                         false
% 2.50/0.99  --bmc1_ucm                              false
% 2.50/0.99  --bmc1_add_unsat_core                   none
% 2.50/0.99  --bmc1_unsat_core_children              false
% 2.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.99  --bmc1_out_stat                         full
% 2.50/0.99  --bmc1_ground_init                      false
% 2.50/0.99  --bmc1_pre_inst_next_state              false
% 2.50/0.99  --bmc1_pre_inst_state                   false
% 2.50/0.99  --bmc1_pre_inst_reach_state             false
% 2.50/0.99  --bmc1_out_unsat_core                   false
% 2.50/0.99  --bmc1_aig_witness_out                  false
% 2.50/0.99  --bmc1_verbose                          false
% 2.50/0.99  --bmc1_dump_clauses_tptp                false
% 2.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.99  --bmc1_dump_file                        -
% 2.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.99  --bmc1_ucm_extend_mode                  1
% 2.50/0.99  --bmc1_ucm_init_mode                    2
% 2.50/0.99  --bmc1_ucm_cone_mode                    none
% 2.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.99  --bmc1_ucm_relax_model                  4
% 2.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.99  --bmc1_ucm_layered_model                none
% 2.50/0.99  --bmc1_ucm_max_lemma_size               10
% 2.50/0.99  
% 2.50/0.99  ------ AIG Options
% 2.50/0.99  
% 2.50/0.99  --aig_mode                              false
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation Options
% 2.50/0.99  
% 2.50/0.99  --instantiation_flag                    true
% 2.50/0.99  --inst_sos_flag                         false
% 2.50/0.99  --inst_sos_phase                        true
% 2.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel_side                     num_symb
% 2.50/0.99  --inst_solver_per_active                1400
% 2.50/0.99  --inst_solver_calls_frac                1.
% 2.50/0.99  --inst_passive_queue_type               priority_queues
% 2.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.99  --inst_passive_queues_freq              [25;2]
% 2.50/0.99  --inst_dismatching                      true
% 2.50/0.99  --inst_eager_unprocessed_to_passive     true
% 2.50/0.99  --inst_prop_sim_given                   true
% 2.50/0.99  --inst_prop_sim_new                     false
% 2.50/0.99  --inst_subs_new                         false
% 2.50/0.99  --inst_eq_res_simp                      false
% 2.50/0.99  --inst_subs_given                       false
% 2.50/0.99  --inst_orphan_elimination               true
% 2.50/0.99  --inst_learning_loop_flag               true
% 2.50/0.99  --inst_learning_start                   3000
% 2.50/0.99  --inst_learning_factor                  2
% 2.50/0.99  --inst_start_prop_sim_after_learn       3
% 2.50/0.99  --inst_sel_renew                        solver
% 2.50/0.99  --inst_lit_activity_flag                true
% 2.50/0.99  --inst_restr_to_given                   false
% 2.50/0.99  --inst_activity_threshold               500
% 2.50/0.99  --inst_out_proof                        true
% 2.50/0.99  
% 2.50/0.99  ------ Resolution Options
% 2.50/0.99  
% 2.50/0.99  --resolution_flag                       true
% 2.50/0.99  --res_lit_sel                           adaptive
% 2.50/0.99  --res_lit_sel_side                      none
% 2.50/0.99  --res_ordering                          kbo
% 2.50/0.99  --res_to_prop_solver                    active
% 2.50/0.99  --res_prop_simpl_new                    false
% 2.50/0.99  --res_prop_simpl_given                  true
% 2.50/0.99  --res_passive_queue_type                priority_queues
% 2.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.99  --res_passive_queues_freq               [15;5]
% 2.50/0.99  --res_forward_subs                      full
% 2.50/0.99  --res_backward_subs                     full
% 2.50/0.99  --res_forward_subs_resolution           true
% 2.50/0.99  --res_backward_subs_resolution          true
% 2.50/0.99  --res_orphan_elimination                true
% 2.50/0.99  --res_time_limit                        2.
% 2.50/0.99  --res_out_proof                         true
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Options
% 2.50/0.99  
% 2.50/0.99  --superposition_flag                    true
% 2.50/0.99  --sup_passive_queue_type                priority_queues
% 2.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.99  --demod_completeness_check              fast
% 2.50/0.99  --demod_use_ground                      true
% 2.50/0.99  --sup_to_prop_solver                    passive
% 2.50/0.99  --sup_prop_simpl_new                    true
% 2.50/0.99  --sup_prop_simpl_given                  true
% 2.50/0.99  --sup_fun_splitting                     false
% 2.50/0.99  --sup_smt_interval                      50000
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Simplification Setup
% 2.50/0.99  
% 2.50/0.99  --sup_indices_passive                   []
% 2.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_full_bw                           [BwDemod]
% 2.50/0.99  --sup_immed_triv                        [TrivRules]
% 2.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_immed_bw_main                     []
% 2.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  
% 2.50/0.99  ------ Combination Options
% 2.50/0.99  
% 2.50/0.99  --comb_res_mult                         3
% 2.50/0.99  --comb_sup_mult                         2
% 2.50/0.99  --comb_inst_mult                        10
% 2.50/0.99  
% 2.50/0.99  ------ Debug Options
% 2.50/0.99  
% 2.50/0.99  --dbg_backtrace                         false
% 2.50/0.99  --dbg_dump_prop_clauses                 false
% 2.50/0.99  --dbg_dump_prop_clauses_file            -
% 2.50/0.99  --dbg_out_stat                          false
% 2.50/0.99  ------ Parsing...
% 2.50/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/0.99  ------ Proving...
% 2.50/0.99  ------ Problem Properties 
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  clauses                                 20
% 2.50/0.99  conjectures                             7
% 2.50/0.99  EPR                                     6
% 2.50/0.99  Horn                                    20
% 2.50/0.99  unary                                   8
% 2.50/0.99  binary                                  2
% 2.50/0.99  lits                                    53
% 2.50/0.99  lits eq                                 8
% 2.50/0.99  fd_pure                                 0
% 2.50/0.99  fd_pseudo                               0
% 2.50/0.99  fd_cond                                 0
% 2.50/0.99  fd_pseudo_cond                          0
% 2.50/0.99  AC symbols                              0
% 2.50/0.99  
% 2.50/0.99  ------ Schedule dynamic 5 is on 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  ------ 
% 2.50/0.99  Current options:
% 2.50/0.99  ------ 
% 2.50/0.99  
% 2.50/0.99  ------ Input Options
% 2.50/0.99  
% 2.50/0.99  --out_options                           all
% 2.50/0.99  --tptp_safe_out                         true
% 2.50/0.99  --problem_path                          ""
% 2.50/0.99  --include_path                          ""
% 2.50/0.99  --clausifier                            res/vclausify_rel
% 2.50/0.99  --clausifier_options                    --mode clausify
% 2.50/0.99  --stdin                                 false
% 2.50/0.99  --stats_out                             all
% 2.50/0.99  
% 2.50/0.99  ------ General Options
% 2.50/0.99  
% 2.50/0.99  --fof                                   false
% 2.50/0.99  --time_out_real                         305.
% 2.50/0.99  --time_out_virtual                      -1.
% 2.50/0.99  --symbol_type_check                     false
% 2.50/0.99  --clausify_out                          false
% 2.50/0.99  --sig_cnt_out                           false
% 2.50/0.99  --trig_cnt_out                          false
% 2.50/0.99  --trig_cnt_out_tolerance                1.
% 2.50/0.99  --trig_cnt_out_sk_spl                   false
% 2.50/0.99  --abstr_cl_out                          false
% 2.50/0.99  
% 2.50/0.99  ------ Global Options
% 2.50/0.99  
% 2.50/0.99  --schedule                              default
% 2.50/0.99  --add_important_lit                     false
% 2.50/0.99  --prop_solver_per_cl                    1000
% 2.50/0.99  --min_unsat_core                        false
% 2.50/0.99  --soft_assumptions                      false
% 2.50/0.99  --soft_lemma_size                       3
% 2.50/0.99  --prop_impl_unit_size                   0
% 2.50/0.99  --prop_impl_unit                        []
% 2.50/0.99  --share_sel_clauses                     true
% 2.50/0.99  --reset_solvers                         false
% 2.50/0.99  --bc_imp_inh                            [conj_cone]
% 2.50/0.99  --conj_cone_tolerance                   3.
% 2.50/0.99  --extra_neg_conj                        none
% 2.50/0.99  --large_theory_mode                     true
% 2.50/0.99  --prolific_symb_bound                   200
% 2.50/0.99  --lt_threshold                          2000
% 2.50/0.99  --clause_weak_htbl                      true
% 2.50/0.99  --gc_record_bc_elim                     false
% 2.50/0.99  
% 2.50/0.99  ------ Preprocessing Options
% 2.50/0.99  
% 2.50/0.99  --preprocessing_flag                    true
% 2.50/0.99  --time_out_prep_mult                    0.1
% 2.50/0.99  --splitting_mode                        input
% 2.50/0.99  --splitting_grd                         true
% 2.50/0.99  --splitting_cvd                         false
% 2.50/0.99  --splitting_cvd_svl                     false
% 2.50/0.99  --splitting_nvd                         32
% 2.50/0.99  --sub_typing                            true
% 2.50/0.99  --prep_gs_sim                           true
% 2.50/0.99  --prep_unflatten                        true
% 2.50/0.99  --prep_res_sim                          true
% 2.50/0.99  --prep_upred                            true
% 2.50/0.99  --prep_sem_filter                       exhaustive
% 2.50/0.99  --prep_sem_filter_out                   false
% 2.50/0.99  --pred_elim                             true
% 2.50/0.99  --res_sim_input                         true
% 2.50/0.99  --eq_ax_congr_red                       true
% 2.50/0.99  --pure_diseq_elim                       true
% 2.50/0.99  --brand_transform                       false
% 2.50/0.99  --non_eq_to_eq                          false
% 2.50/0.99  --prep_def_merge                        true
% 2.50/0.99  --prep_def_merge_prop_impl              false
% 2.50/0.99  --prep_def_merge_mbd                    true
% 2.50/0.99  --prep_def_merge_tr_red                 false
% 2.50/0.99  --prep_def_merge_tr_cl                  false
% 2.50/0.99  --smt_preprocessing                     true
% 2.50/0.99  --smt_ac_axioms                         fast
% 2.50/0.99  --preprocessed_out                      false
% 2.50/0.99  --preprocessed_stats                    false
% 2.50/0.99  
% 2.50/0.99  ------ Abstraction refinement Options
% 2.50/0.99  
% 2.50/0.99  --abstr_ref                             []
% 2.50/0.99  --abstr_ref_prep                        false
% 2.50/0.99  --abstr_ref_until_sat                   false
% 2.50/0.99  --abstr_ref_sig_restrict                funpre
% 2.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.99  --abstr_ref_under                       []
% 2.50/0.99  
% 2.50/0.99  ------ SAT Options
% 2.50/0.99  
% 2.50/0.99  --sat_mode                              false
% 2.50/0.99  --sat_fm_restart_options                ""
% 2.50/0.99  --sat_gr_def                            false
% 2.50/0.99  --sat_epr_types                         true
% 2.50/0.99  --sat_non_cyclic_types                  false
% 2.50/0.99  --sat_finite_models                     false
% 2.50/0.99  --sat_fm_lemmas                         false
% 2.50/0.99  --sat_fm_prep                           false
% 2.50/0.99  --sat_fm_uc_incr                        true
% 2.50/0.99  --sat_out_model                         small
% 2.50/0.99  --sat_out_clauses                       false
% 2.50/0.99  
% 2.50/0.99  ------ QBF Options
% 2.50/0.99  
% 2.50/0.99  --qbf_mode                              false
% 2.50/0.99  --qbf_elim_univ                         false
% 2.50/0.99  --qbf_dom_inst                          none
% 2.50/0.99  --qbf_dom_pre_inst                      false
% 2.50/0.99  --qbf_sk_in                             false
% 2.50/0.99  --qbf_pred_elim                         true
% 2.50/0.99  --qbf_split                             512
% 2.50/0.99  
% 2.50/0.99  ------ BMC1 Options
% 2.50/0.99  
% 2.50/0.99  --bmc1_incremental                      false
% 2.50/0.99  --bmc1_axioms                           reachable_all
% 2.50/0.99  --bmc1_min_bound                        0
% 2.50/0.99  --bmc1_max_bound                        -1
% 2.50/0.99  --bmc1_max_bound_default                -1
% 2.50/0.99  --bmc1_symbol_reachability              true
% 2.50/0.99  --bmc1_property_lemmas                  false
% 2.50/0.99  --bmc1_k_induction                      false
% 2.50/0.99  --bmc1_non_equiv_states                 false
% 2.50/0.99  --bmc1_deadlock                         false
% 2.50/0.99  --bmc1_ucm                              false
% 2.50/0.99  --bmc1_add_unsat_core                   none
% 2.50/0.99  --bmc1_unsat_core_children              false
% 2.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.99  --bmc1_out_stat                         full
% 2.50/0.99  --bmc1_ground_init                      false
% 2.50/0.99  --bmc1_pre_inst_next_state              false
% 2.50/0.99  --bmc1_pre_inst_state                   false
% 2.50/0.99  --bmc1_pre_inst_reach_state             false
% 2.50/0.99  --bmc1_out_unsat_core                   false
% 2.50/0.99  --bmc1_aig_witness_out                  false
% 2.50/0.99  --bmc1_verbose                          false
% 2.50/0.99  --bmc1_dump_clauses_tptp                false
% 2.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.99  --bmc1_dump_file                        -
% 2.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.99  --bmc1_ucm_extend_mode                  1
% 2.50/0.99  --bmc1_ucm_init_mode                    2
% 2.50/0.99  --bmc1_ucm_cone_mode                    none
% 2.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.99  --bmc1_ucm_relax_model                  4
% 2.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.99  --bmc1_ucm_layered_model                none
% 2.50/0.99  --bmc1_ucm_max_lemma_size               10
% 2.50/0.99  
% 2.50/0.99  ------ AIG Options
% 2.50/0.99  
% 2.50/0.99  --aig_mode                              false
% 2.50/0.99  
% 2.50/0.99  ------ Instantiation Options
% 2.50/0.99  
% 2.50/0.99  --instantiation_flag                    true
% 2.50/0.99  --inst_sos_flag                         false
% 2.50/0.99  --inst_sos_phase                        true
% 2.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.99  --inst_lit_sel_side                     none
% 2.50/0.99  --inst_solver_per_active                1400
% 2.50/0.99  --inst_solver_calls_frac                1.
% 2.50/0.99  --inst_passive_queue_type               priority_queues
% 2.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.99  --inst_passive_queues_freq              [25;2]
% 2.50/0.99  --inst_dismatching                      true
% 2.50/0.99  --inst_eager_unprocessed_to_passive     true
% 2.50/0.99  --inst_prop_sim_given                   true
% 2.50/0.99  --inst_prop_sim_new                     false
% 2.50/0.99  --inst_subs_new                         false
% 2.50/0.99  --inst_eq_res_simp                      false
% 2.50/0.99  --inst_subs_given                       false
% 2.50/0.99  --inst_orphan_elimination               true
% 2.50/0.99  --inst_learning_loop_flag               true
% 2.50/0.99  --inst_learning_start                   3000
% 2.50/0.99  --inst_learning_factor                  2
% 2.50/0.99  --inst_start_prop_sim_after_learn       3
% 2.50/0.99  --inst_sel_renew                        solver
% 2.50/0.99  --inst_lit_activity_flag                true
% 2.50/0.99  --inst_restr_to_given                   false
% 2.50/0.99  --inst_activity_threshold               500
% 2.50/0.99  --inst_out_proof                        true
% 2.50/0.99  
% 2.50/0.99  ------ Resolution Options
% 2.50/0.99  
% 2.50/0.99  --resolution_flag                       false
% 2.50/0.99  --res_lit_sel                           adaptive
% 2.50/0.99  --res_lit_sel_side                      none
% 2.50/0.99  --res_ordering                          kbo
% 2.50/0.99  --res_to_prop_solver                    active
% 2.50/0.99  --res_prop_simpl_new                    false
% 2.50/0.99  --res_prop_simpl_given                  true
% 2.50/0.99  --res_passive_queue_type                priority_queues
% 2.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.99  --res_passive_queues_freq               [15;5]
% 2.50/0.99  --res_forward_subs                      full
% 2.50/0.99  --res_backward_subs                     full
% 2.50/0.99  --res_forward_subs_resolution           true
% 2.50/0.99  --res_backward_subs_resolution          true
% 2.50/0.99  --res_orphan_elimination                true
% 2.50/0.99  --res_time_limit                        2.
% 2.50/0.99  --res_out_proof                         true
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Options
% 2.50/0.99  
% 2.50/0.99  --superposition_flag                    true
% 2.50/0.99  --sup_passive_queue_type                priority_queues
% 2.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.99  --demod_completeness_check              fast
% 2.50/0.99  --demod_use_ground                      true
% 2.50/0.99  --sup_to_prop_solver                    passive
% 2.50/0.99  --sup_prop_simpl_new                    true
% 2.50/0.99  --sup_prop_simpl_given                  true
% 2.50/0.99  --sup_fun_splitting                     false
% 2.50/0.99  --sup_smt_interval                      50000
% 2.50/0.99  
% 2.50/0.99  ------ Superposition Simplification Setup
% 2.50/0.99  
% 2.50/0.99  --sup_indices_passive                   []
% 2.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_full_bw                           [BwDemod]
% 2.50/0.99  --sup_immed_triv                        [TrivRules]
% 2.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_immed_bw_main                     []
% 2.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.99  
% 2.50/0.99  ------ Combination Options
% 2.50/0.99  
% 2.50/0.99  --comb_res_mult                         3
% 2.50/0.99  --comb_sup_mult                         2
% 2.50/0.99  --comb_inst_mult                        10
% 2.50/0.99  
% 2.50/0.99  ------ Debug Options
% 2.50/0.99  
% 2.50/0.99  --dbg_backtrace                         false
% 2.50/0.99  --dbg_dump_prop_clauses                 false
% 2.50/0.99  --dbg_dump_prop_clauses_file            -
% 2.50/0.99  --dbg_out_stat                          false
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  ------ Proving...
% 2.50/0.99  
% 2.50/0.99  
% 2.50/0.99  % SZS status Theorem for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/0.99  
% 2.50/0.99  fof(f1,axiom,(
% 2.50/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f45,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f1])).
% 2.50/0.99  
% 2.50/0.99  fof(f10,conjecture,(
% 2.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f11,negated_conjecture,(
% 2.50/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 2.50/0.99    inference(negated_conjecture,[],[f10])).
% 2.50/0.99  
% 2.50/0.99  fof(f22,plain,(
% 2.50/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.50/0.99    inference(ennf_transformation,[],[f11])).
% 2.50/0.99  
% 2.50/0.99  fof(f23,plain,(
% 2.50/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.50/0.99    inference(flattening,[],[f22])).
% 2.50/0.99  
% 2.50/0.99  fof(f43,plain,(
% 2.50/0.99    ( ! [X2,X1] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v4_pre_topc(sK9,X2) & sK9 = X1 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f42,plain,(
% 2.50/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v4_pre_topc(X3,sK8) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) & v4_pre_topc(X1,X0) & m1_pre_topc(sK8,X0))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f41,plain,(
% 2.50/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK7,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f40,plain,(
% 2.50/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f44,plain,(
% 2.50/0.99    (((~v4_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & v4_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6)),
% 2.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f23,f43,f42,f41,f40])).
% 2.50/0.99  
% 2.50/0.99  fof(f75,plain,(
% 2.50/0.99    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 2.50/0.99    inference(cnf_transformation,[],[f44])).
% 2.50/0.99  
% 2.50/0.99  fof(f7,axiom,(
% 2.50/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f18,plain,(
% 2.50/0.99    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.50/0.99    inference(ennf_transformation,[],[f7])).
% 2.50/0.99  
% 2.50/0.99  fof(f19,plain,(
% 2.50/0.99    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(flattening,[],[f18])).
% 2.50/0.99  
% 2.50/0.99  fof(f65,plain,(
% 2.50/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f19])).
% 2.50/0.99  
% 2.50/0.99  fof(f71,plain,(
% 2.50/0.99    l1_pre_topc(sK6)),
% 2.50/0.99    inference(cnf_transformation,[],[f44])).
% 2.50/0.99  
% 2.50/0.99  fof(f8,axiom,(
% 2.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f20,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(ennf_transformation,[],[f8])).
% 2.50/0.99  
% 2.50/0.99  fof(f66,plain,(
% 2.50/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f20])).
% 2.50/0.99  
% 2.50/0.99  fof(f73,plain,(
% 2.50/0.99    m1_pre_topc(sK8,sK6)),
% 2.50/0.99    inference(cnf_transformation,[],[f44])).
% 2.50/0.99  
% 2.50/0.99  fof(f6,axiom,(
% 2.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f17,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(ennf_transformation,[],[f6])).
% 2.50/0.99  
% 2.50/0.99  fof(f25,plain,(
% 2.50/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 2.50/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.50/0.99  
% 2.50/0.99  fof(f24,plain,(
% 2.50/0.99    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 2.50/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.50/0.99  
% 2.50/0.99  fof(f26,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(definition_folding,[],[f17,f25,f24])).
% 2.50/0.99  
% 2.50/0.99  fof(f63,plain,(
% 2.50/0.99    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f26])).
% 2.50/0.99  
% 2.50/0.99  fof(f28,plain,(
% 2.50/0.99    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 2.50/0.99    inference(nnf_transformation,[],[f25])).
% 2.50/0.99  
% 2.50/0.99  fof(f51,plain,(
% 2.50/0.99    ( ! [X0,X1] : (sP0(X1,X0) | ~m1_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f28])).
% 2.50/0.99  
% 2.50/0.99  fof(f2,axiom,(
% 2.50/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f12,plain,(
% 2.50/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.50/0.99    inference(ennf_transformation,[],[f2])).
% 2.50/0.99  
% 2.50/0.99  fof(f46,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f12])).
% 2.50/0.99  
% 2.50/0.99  fof(f29,plain,(
% 2.50/0.99    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.50/0.99    inference(nnf_transformation,[],[f24])).
% 2.50/0.99  
% 2.50/0.99  fof(f30,plain,(
% 2.50/0.99    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 2.50/0.99    inference(flattening,[],[f29])).
% 2.50/0.99  
% 2.50/0.99  fof(f31,plain,(
% 2.50/0.99    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.50/0.99    inference(rectify,[],[f30])).
% 2.50/0.99  
% 2.50/0.99  fof(f34,plain,(
% 2.50/0.99    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f33,plain,(
% 2.50/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = X2 & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f32,plain,(
% 2.50/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f35,plain,(
% 2.50/0.99    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK2(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & ((k9_subset_1(u1_struct_0(X0),sK3(X0,X1),k2_struct_0(X0)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK2(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK4(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK4(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK4(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 2.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f34,f33,f32])).
% 2.50/0.99  
% 2.50/0.99  fof(f53,plain,(
% 2.50/0.99    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f35])).
% 2.50/0.99  
% 2.50/0.99  fof(f5,axiom,(
% 2.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f15,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(ennf_transformation,[],[f5])).
% 2.50/0.99  
% 2.50/0.99  fof(f16,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(flattening,[],[f15])).
% 2.50/0.99  
% 2.50/0.99  fof(f27,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(nnf_transformation,[],[f16])).
% 2.50/0.99  
% 2.50/0.99  fof(f49,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f27])).
% 2.50/0.99  
% 2.50/0.99  fof(f79,plain,(
% 2.50/0.99    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.50/0.99    inference(equality_resolution,[],[f49])).
% 2.50/0.99  
% 2.50/0.99  fof(f64,plain,(
% 2.50/0.99    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f19])).
% 2.50/0.99  
% 2.50/0.99  fof(f3,axiom,(
% 2.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f13,plain,(
% 2.50/0.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.50/0.99    inference(ennf_transformation,[],[f3])).
% 2.50/0.99  
% 2.50/0.99  fof(f47,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f13])).
% 2.50/0.99  
% 2.50/0.99  fof(f4,axiom,(
% 2.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f14,plain,(
% 2.50/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.50/0.99    inference(ennf_transformation,[],[f4])).
% 2.50/0.99  
% 2.50/0.99  fof(f48,plain,(
% 2.50/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.50/0.99    inference(cnf_transformation,[],[f14])).
% 2.50/0.99  
% 2.50/0.99  fof(f9,axiom,(
% 2.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/0.99  
% 2.50/0.99  fof(f21,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(ennf_transformation,[],[f9])).
% 2.50/0.99  
% 2.50/0.99  fof(f36,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(nnf_transformation,[],[f21])).
% 2.50/0.99  
% 2.50/0.99  fof(f37,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(rectify,[],[f36])).
% 2.50/0.99  
% 2.50/0.99  fof(f38,plain,(
% 2.50/0.99    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/0.99    introduced(choice_axiom,[])).
% 2.50/0.99  
% 2.50/0.99  fof(f39,plain,(
% 2.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 2.50/0.99  
% 2.50/0.99  fof(f70,plain,(
% 2.50/0.99    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.50/0.99    inference(cnf_transformation,[],[f39])).
% 2.50/0.99  
% 2.50/0.99  fof(f81,plain,(
% 2.50/0.99    ( ! [X0,X3,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.50/0.99    inference(equality_resolution,[],[f70])).
% 2.50/0.99  
% 2.50/0.99  fof(f72,plain,(
% 2.50/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 2.50/0.99    inference(cnf_transformation,[],[f44])).
% 2.50/0.99  
% 2.50/0.99  fof(f76,plain,(
% 2.50/0.99    sK7 = sK9),
% 2.50/0.99    inference(cnf_transformation,[],[f44])).
% 2.50/0.99  
% 2.50/0.99  fof(f74,plain,(
% 2.50/0.99    v4_pre_topc(sK7,sK6)),
% 2.50/0.99    inference(cnf_transformation,[],[f44])).
% 2.50/0.99  
% 2.50/0.99  fof(f77,plain,(
% 2.50/0.99    ~v4_pre_topc(sK9,sK8)),
% 2.50/0.99    inference(cnf_transformation,[],[f44])).
% 2.50/0.99  
% 2.50/0.99  cnf(c_0,plain,
% 2.50/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1906,plain,
% 2.50/0.99      ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_28,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 2.50/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1893,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_28]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2296,plain,
% 2.50/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1893]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_19,plain,
% 2.50/0.99      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 2.50/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.50/0.99      | ~ l1_pre_topc(X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1902,plain,
% 2.50/0.99      ( m1_pre_topc(k1_pre_topc(X0_52,X0_53),X0_52)
% 2.50/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.50/0.99      | ~ l1_pre_topc(X0_52) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2288,plain,
% 2.50/0.99      ( m1_pre_topc(k1_pre_topc(X0_52,X0_53),X0_52) = iProver_top
% 2.50/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.50/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1902]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2766,plain,
% 2.50/0.99      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top
% 2.50/0.99      | l1_pre_topc(sK8) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2296,c_2288]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_32,negated_conjecture,
% 2.50/0.99      ( l1_pre_topc(sK6) ),
% 2.50/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_33,plain,
% 2.50/0.99      ( l1_pre_topc(sK6) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_21,plain,
% 2.50/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_30,negated_conjecture,
% 2.50/0.99      ( m1_pre_topc(sK8,sK6) ),
% 2.50/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_679,plain,
% 2.50/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X0 | sK8 != X1 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_680,plain,
% 2.50/0.99      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_679]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_681,plain,
% 2.50/0.99      ( l1_pre_topc(sK6) != iProver_top
% 2.50/0.99      | l1_pre_topc(sK8) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2990,plain,
% 2.50/0.99      ( m1_pre_topc(k1_pre_topc(sK8,sK9),sK8) = iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_2766,c_33,c_681]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_18,plain,
% 2.50/0.99      ( sP1(X0,X1) | ~ l1_pre_topc(X0) | ~ l1_pre_topc(X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_7,plain,
% 2.50/0.99      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ m1_pre_topc(X1,X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_391,plain,
% 2.50/0.99      ( sP0(X0,X1)
% 2.50/0.99      | ~ m1_pre_topc(X0,X1)
% 2.50/0.99      | ~ l1_pre_topc(X0)
% 2.50/0.99      | ~ l1_pre_topc(X1) ),
% 2.50/0.99      inference(resolution,[status(thm)],[c_18,c_7]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_395,plain,
% 2.50/0.99      ( ~ m1_pre_topc(X0,X1) | sP0(X0,X1) | ~ l1_pre_topc(X1) ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_391,c_21]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_396,plain,
% 2.50/0.99      ( sP0(X0,X1) | ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_395]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1,plain,
% 2.50/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.50/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_17,plain,
% 2.50/0.99      ( ~ sP0(X0,X1) | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_439,plain,
% 2.50/0.99      ( ~ sP0(X0,X1)
% 2.50/0.99      | k3_xboole_0(X2,X3) = X2
% 2.50/0.99      | k2_struct_0(X1) != X3
% 2.50/0.99      | k2_struct_0(X0) != X2 ),
% 2.50/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_440,plain,
% 2.50/0.99      ( ~ sP0(X0,X1)
% 2.50/0.99      | k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0) ),
% 2.50/0.99      inference(unflattening,[status(thm)],[c_439]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1152,plain,
% 2.50/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.50/0.99      | ~ l1_pre_topc(X1)
% 2.50/0.99      | k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) = k2_struct_0(X0) ),
% 2.50/0.99      inference(resolution,[status(thm)],[c_396,c_440]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1887,plain,
% 2.50/0.99      ( ~ m1_pre_topc(X0_52,X1_52)
% 2.50/0.99      | ~ l1_pre_topc(X1_52)
% 2.50/0.99      | k3_xboole_0(k2_struct_0(X0_52),k2_struct_0(X1_52)) = k2_struct_0(X0_52) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_1152]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2302,plain,
% 2.50/0.99      ( k3_xboole_0(k2_struct_0(X0_52),k2_struct_0(X1_52)) = k2_struct_0(X0_52)
% 2.50/0.99      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 2.50/0.99      | l1_pre_topc(X1_52) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1887]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4227,plain,
% 2.50/0.99      ( k3_xboole_0(k2_struct_0(k1_pre_topc(sK8,sK9)),k2_struct_0(sK8)) = k2_struct_0(k1_pre_topc(sK8,sK9))
% 2.50/0.99      | l1_pre_topc(sK8) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2990,c_2302]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_5,plain,
% 2.50/0.99      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 2.50/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.50/0.99      | ~ l1_pre_topc(X0)
% 2.50/0.99      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 2.50/0.99      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 2.50/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_202,plain,
% 2.50/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.50/0.99      | ~ l1_pre_topc(X0)
% 2.50/0.99      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 2.50/0.99      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_5,c_19]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_203,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | ~ l1_pre_topc(X1)
% 2.50/0.99      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 2.50/0.99      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_202]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_20,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | ~ l1_pre_topc(X1)
% 2.50/0.99      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 2.50/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_208,plain,
% 2.50/0.99      ( ~ l1_pre_topc(X1)
% 2.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_203,c_20]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_209,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | ~ l1_pre_topc(X1)
% 2.50/0.99      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 2.50/0.99      inference(renaming,[status(thm)],[c_208]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1888,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.50/0.99      | ~ l1_pre_topc(X0_52)
% 2.50/0.99      | k2_struct_0(k1_pre_topc(X0_52,X0_53)) = X0_53 ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_209]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2301,plain,
% 2.50/0.99      ( k2_struct_0(k1_pre_topc(X0_52,X0_53)) = X0_53
% 2.50/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.50/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1888]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3700,plain,
% 2.50/0.99      ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9
% 2.50/0.99      | l1_pre_topc(sK8) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2296,c_2301]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3727,plain,
% 2.50/0.99      ( k2_struct_0(k1_pre_topc(sK8,sK9)) = sK9 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_3700,c_33,c_681]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4247,plain,
% 2.50/0.99      ( k3_xboole_0(sK9,k2_struct_0(sK8)) = sK9
% 2.50/0.99      | l1_pre_topc(sK8) != iProver_top ),
% 2.50/0.99      inference(light_normalisation,[status(thm)],[c_4227,c_3727]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4674,plain,
% 2.50/0.99      ( k3_xboole_0(sK9,k2_struct_0(sK8)) = sK9 ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_4247,c_33,c_681]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/0.99      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1905,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X0_55))
% 2.50/0.99      | k9_subset_1(X0_55,X0_53,X1_53) = k9_subset_1(X0_55,X1_53,X0_53) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2285,plain,
% 2.50/0.99      ( k9_subset_1(X0_55,X0_53,X1_53) = k9_subset_1(X0_55,X1_53,X0_53)
% 2.50/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(X0_55)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1905]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2620,plain,
% 2.50/0.99      ( k9_subset_1(u1_struct_0(sK8),sK9,X0_53) = k9_subset_1(u1_struct_0(sK8),X0_53,sK9) ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2296,c_2285]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 2.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1904,plain,
% 2.50/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X0_55))
% 2.50/0.99      | k9_subset_1(X0_55,X1_53,X0_53) = k3_xboole_0(X1_53,X0_53) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2286,plain,
% 2.50/0.99      ( k9_subset_1(X0_55,X0_53,X1_53) = k3_xboole_0(X0_53,X1_53)
% 2.50/0.99      | m1_subset_1(X1_53,k1_zfmisc_1(X0_55)) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1904]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2631,plain,
% 2.50/0.99      ( k9_subset_1(u1_struct_0(sK8),X0_53,sK9) = k3_xboole_0(X0_53,sK9) ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2296,c_2286]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2882,plain,
% 2.50/0.99      ( k9_subset_1(u1_struct_0(sK8),sK9,X0_53) = k3_xboole_0(X0_53,sK9) ),
% 2.50/0.99      inference(light_normalisation,[status(thm)],[c_2620,c_2631]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_22,plain,
% 2.50/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.50/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 2.50/0.99      | ~ m1_pre_topc(X2,X1)
% 2.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.50/0.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 2.50/0.99      | ~ l1_pre_topc(X1) ),
% 2.50/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1899,plain,
% 2.50/0.99      ( ~ v4_pre_topc(X0_53,X0_52)
% 2.50/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(X1_52),X0_53,k2_struct_0(X1_52)),X1_52)
% 2.50/0.99      | ~ m1_pre_topc(X1_52,X0_52)
% 2.50/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.50/0.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1_52),X0_53,k2_struct_0(X1_52)),k1_zfmisc_1(u1_struct_0(X1_52)))
% 2.50/0.99      | ~ l1_pre_topc(X0_52) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2291,plain,
% 2.50/0.99      ( v4_pre_topc(X0_53,X0_52) != iProver_top
% 2.50/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(X1_52),X0_53,k2_struct_0(X1_52)),X1_52) = iProver_top
% 2.50/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.50/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.50/0.99      | m1_subset_1(k9_subset_1(u1_struct_0(X1_52),X0_53,k2_struct_0(X1_52)),k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
% 2.50/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3246,plain,
% 2.50/0.99      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8) = iProver_top
% 2.50/0.99      | v4_pre_topc(sK9,X0_52) != iProver_top
% 2.50/0.99      | m1_pre_topc(sK8,X0_52) != iProver_top
% 2.50/0.99      | m1_subset_1(k3_xboole_0(k2_struct_0(sK8),sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 2.50/0.99      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.50/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_2882,c_2291]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3267,plain,
% 2.50/0.99      ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
% 2.50/0.99      | v4_pre_topc(sK9,X0_52) != iProver_top
% 2.50/0.99      | m1_pre_topc(sK8,X0_52) != iProver_top
% 2.50/0.99      | m1_subset_1(k3_xboole_0(k2_struct_0(sK8),sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 2.50/0.99      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0_52))) != iProver_top
% 2.50/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 2.50/0.99      inference(demodulation,[status(thm)],[c_3246,c_2882]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_35,plain,
% 2.50/0.99      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_31,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 2.50/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1890,negated_conjecture,
% 2.50/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_31]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2299,plain,
% 2.50/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1890]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_27,negated_conjecture,
% 2.50/0.99      ( sK7 = sK9 ),
% 2.50/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1894,negated_conjecture,
% 2.50/0.99      ( sK7 = sK9 ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2318,plain,
% 2.50/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 2.50/0.99      inference(light_normalisation,[status(thm)],[c_2299,c_1894]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_29,negated_conjecture,
% 2.50/0.99      ( v4_pre_topc(sK7,sK6) ),
% 2.50/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_1892,negated_conjecture,
% 2.50/0.99      ( v4_pre_topc(sK7,sK6) ),
% 2.50/0.99      inference(subtyping,[status(esa)],[c_29]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2297,plain,
% 2.50/0.99      ( v4_pre_topc(sK7,sK6) = iProver_top ),
% 2.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_2307,plain,
% 2.50/0.99      ( v4_pre_topc(sK9,sK6) = iProver_top ),
% 2.50/0.99      inference(light_normalisation,[status(thm)],[c_2297,c_1894]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3278,plain,
% 2.50/0.99      ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
% 2.50/0.99      | v4_pre_topc(sK9,sK6) != iProver_top
% 2.50/0.99      | m1_pre_topc(sK8,sK6) != iProver_top
% 2.50/0.99      | m1_subset_1(k3_xboole_0(k2_struct_0(sK8),sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 2.50/0.99      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 2.50/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 2.50/0.99      inference(instantiation,[status(thm)],[c_3267]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3500,plain,
% 2.50/0.99      ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
% 2.50/0.99      | m1_subset_1(k3_xboole_0(k2_struct_0(sK8),sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 2.50/0.99      inference(global_propositional_subsumption,
% 2.50/0.99                [status(thm)],
% 2.50/0.99                [c_3267,c_33,c_35,c_2318,c_2307,c_3278]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_3506,plain,
% 2.50/0.99      ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
% 2.50/0.99      | m1_subset_1(k3_xboole_0(sK9,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 2.50/0.99      inference(superposition,[status(thm)],[c_1906,c_3500]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_4677,plain,
% 2.50/0.99      ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top
% 2.50/0.99      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 2.50/0.99      inference(demodulation,[status(thm)],[c_4674,c_3506]) ).
% 2.50/0.99  
% 2.50/0.99  cnf(c_37,plain,
% 2.50/0.99      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 2.50/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_4781,plain,
% 2.50/1.00      ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK8),sK9),sK8) = iProver_top ),
% 2.50/1.00      inference(global_propositional_subsumption,
% 2.50/1.00                [status(thm)],
% 2.50/1.00                [c_4677,c_37]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_4786,plain,
% 2.50/1.00      ( v4_pre_topc(k3_xboole_0(sK9,k2_struct_0(sK8)),sK8) = iProver_top ),
% 2.50/1.00      inference(superposition,[status(thm)],[c_1906,c_4781]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_4788,plain,
% 2.50/1.00      ( v4_pre_topc(sK9,sK8) = iProver_top ),
% 2.50/1.00      inference(light_normalisation,[status(thm)],[c_4786,c_4674]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_26,negated_conjecture,
% 2.50/1.00      ( ~ v4_pre_topc(sK9,sK8) ),
% 2.50/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(c_38,plain,
% 2.50/1.00      ( v4_pre_topc(sK9,sK8) != iProver_top ),
% 2.50/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.50/1.00  
% 2.50/1.00  cnf(contradiction,plain,
% 2.50/1.00      ( $false ),
% 2.50/1.00      inference(minisat,[status(thm)],[c_4788,c_38]) ).
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/1.00  
% 2.50/1.00  ------                               Statistics
% 2.50/1.00  
% 2.50/1.00  ------ General
% 2.50/1.00  
% 2.50/1.00  abstr_ref_over_cycles:                  0
% 2.50/1.00  abstr_ref_under_cycles:                 0
% 2.50/1.00  gc_basic_clause_elim:                   0
% 2.50/1.00  forced_gc_time:                         0
% 2.50/1.00  parsing_time:                           0.011
% 2.50/1.00  unif_index_cands_time:                  0.
% 2.50/1.00  unif_index_add_time:                    0.
% 2.50/1.00  orderings_time:                         0.
% 2.50/1.00  out_proof_time:                         0.009
% 2.50/1.00  total_time:                             0.169
% 2.50/1.00  num_of_symbols:                         62
% 2.50/1.00  num_of_terms:                           4324
% 2.50/1.00  
% 2.50/1.00  ------ Preprocessing
% 2.50/1.00  
% 2.50/1.00  num_of_splits:                          0
% 2.50/1.00  num_of_split_atoms:                     0
% 2.50/1.00  num_of_reused_defs:                     0
% 2.50/1.00  num_eq_ax_congr_red:                    38
% 2.50/1.00  num_of_sem_filtered_clauses:            6
% 2.50/1.00  num_of_subtypes:                        4
% 2.50/1.00  monotx_restored_types:                  0
% 2.50/1.00  sat_num_of_epr_types:                   0
% 2.50/1.00  sat_num_of_non_cyclic_types:            0
% 2.50/1.00  sat_guarded_non_collapsed_types:        2
% 2.50/1.00  num_pure_diseq_elim:                    0
% 2.50/1.00  simp_replaced_by:                       0
% 2.50/1.00  res_preprocessed:                       155
% 2.50/1.00  prep_upred:                             0
% 2.50/1.00  prep_unflattend:                        97
% 2.50/1.00  smt_new_axioms:                         0
% 2.50/1.00  pred_elim_cands:                        5
% 2.50/1.00  pred_elim:                              3
% 2.50/1.00  pred_elim_cl:                           8
% 2.50/1.00  pred_elim_cycles:                       9
% 2.50/1.00  merged_defs:                            0
% 2.50/1.00  merged_defs_ncl:                        0
% 2.50/1.00  bin_hyper_res:                          0
% 2.50/1.00  prep_cycles:                            5
% 2.50/1.00  pred_elim_time:                         0.025
% 2.50/1.00  splitting_time:                         0.
% 2.50/1.00  sem_filter_time:                        0.
% 2.50/1.00  monotx_time:                            0.
% 2.50/1.00  subtype_inf_time:                       0.
% 2.50/1.00  
% 2.50/1.00  ------ Problem properties
% 2.50/1.00  
% 2.50/1.00  clauses:                                20
% 2.50/1.00  conjectures:                            7
% 2.50/1.00  epr:                                    6
% 2.50/1.00  horn:                                   20
% 2.50/1.00  ground:                                 7
% 2.50/1.00  unary:                                  8
% 2.50/1.00  binary:                                 2
% 2.50/1.00  lits:                                   53
% 2.50/1.00  lits_eq:                                8
% 2.50/1.00  fd_pure:                                0
% 2.50/1.00  fd_pseudo:                              0
% 2.50/1.00  fd_cond:                                0
% 2.50/1.00  fd_pseudo_cond:                         0
% 2.50/1.00  ac_symbols:                             0
% 2.50/1.00  
% 2.50/1.00  ------ Propositional Solver
% 2.50/1.00  
% 2.50/1.00  prop_solver_calls:                      33
% 2.50/1.00  prop_fast_solver_calls:                 1377
% 2.50/1.00  smt_solver_calls:                       0
% 2.50/1.00  smt_fast_solver_calls:                  0
% 2.50/1.00  prop_num_of_clauses:                    1335
% 2.50/1.00  prop_preprocess_simplified:             5684
% 2.50/1.00  prop_fo_subsumed:                       49
% 2.50/1.00  prop_solver_time:                       0.
% 2.50/1.00  smt_solver_time:                        0.
% 2.50/1.00  smt_fast_solver_time:                   0.
% 2.50/1.00  prop_fast_solver_time:                  0.
% 2.50/1.00  prop_unsat_core_time:                   0.
% 2.50/1.00  
% 2.50/1.00  ------ QBF
% 2.50/1.00  
% 2.50/1.00  qbf_q_res:                              0
% 2.50/1.00  qbf_num_tautologies:                    0
% 2.50/1.00  qbf_prep_cycles:                        0
% 2.50/1.00  
% 2.50/1.00  ------ BMC1
% 2.50/1.00  
% 2.50/1.00  bmc1_current_bound:                     -1
% 2.50/1.00  bmc1_last_solved_bound:                 -1
% 2.50/1.00  bmc1_unsat_core_size:                   -1
% 2.50/1.00  bmc1_unsat_core_parents_size:           -1
% 2.50/1.00  bmc1_merge_next_fun:                    0
% 2.50/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.50/1.00  
% 2.50/1.00  ------ Instantiation
% 2.50/1.00  
% 2.50/1.00  inst_num_of_clauses:                    401
% 2.50/1.00  inst_num_in_passive:                    65
% 2.50/1.00  inst_num_in_active:                     257
% 2.50/1.00  inst_num_in_unprocessed:                79
% 2.50/1.00  inst_num_of_loops:                      270
% 2.50/1.00  inst_num_of_learning_restarts:          0
% 2.50/1.00  inst_num_moves_active_passive:          8
% 2.50/1.00  inst_lit_activity:                      0
% 2.50/1.00  inst_lit_activity_moves:                0
% 2.50/1.00  inst_num_tautologies:                   0
% 2.50/1.00  inst_num_prop_implied:                  0
% 2.50/1.00  inst_num_existing_simplified:           0
% 2.50/1.00  inst_num_eq_res_simplified:             0
% 2.50/1.00  inst_num_child_elim:                    0
% 2.50/1.00  inst_num_of_dismatching_blockings:      135
% 2.50/1.00  inst_num_of_non_proper_insts:           461
% 2.50/1.00  inst_num_of_duplicates:                 0
% 2.50/1.00  inst_inst_num_from_inst_to_res:         0
% 2.50/1.00  inst_dismatching_checking_time:         0.
% 2.50/1.00  
% 2.50/1.00  ------ Resolution
% 2.50/1.00  
% 2.50/1.00  res_num_of_clauses:                     0
% 2.50/1.00  res_num_in_passive:                     0
% 2.50/1.00  res_num_in_active:                      0
% 2.50/1.00  res_num_of_loops:                       160
% 2.50/1.00  res_forward_subset_subsumed:            19
% 2.50/1.00  res_backward_subset_subsumed:           2
% 2.50/1.00  res_forward_subsumed:                   0
% 2.50/1.00  res_backward_subsumed:                  0
% 2.50/1.00  res_forward_subsumption_resolution:     0
% 2.50/1.00  res_backward_subsumption_resolution:    0
% 2.50/1.00  res_clause_to_clause_subsumption:       154
% 2.50/1.00  res_orphan_elimination:                 0
% 2.50/1.00  res_tautology_del:                      43
% 2.50/1.00  res_num_eq_res_simplified:              0
% 2.50/1.00  res_num_sel_changes:                    0
% 2.50/1.00  res_moves_from_active_to_pass:          0
% 2.50/1.00  
% 2.50/1.00  ------ Superposition
% 2.50/1.00  
% 2.50/1.00  sup_time_total:                         0.
% 2.50/1.00  sup_time_generating:                    0.
% 2.50/1.00  sup_time_sim_full:                      0.
% 2.50/1.00  sup_time_sim_immed:                     0.
% 2.50/1.00  
% 2.50/1.00  sup_num_of_clauses:                     59
% 2.50/1.00  sup_num_in_active:                      50
% 2.50/1.00  sup_num_in_passive:                     9
% 2.50/1.00  sup_num_of_loops:                       52
% 2.50/1.00  sup_fw_superposition:                   35
% 2.50/1.00  sup_bw_superposition:                   11
% 2.50/1.00  sup_immediate_simplified:               12
% 2.50/1.00  sup_given_eliminated:                   0
% 2.50/1.00  comparisons_done:                       0
% 2.50/1.00  comparisons_avoided:                    0
% 2.50/1.00  
% 2.50/1.00  ------ Simplifications
% 2.50/1.00  
% 2.50/1.00  
% 2.50/1.00  sim_fw_subset_subsumed:                 3
% 2.50/1.00  sim_bw_subset_subsumed:                 1
% 2.50/1.00  sim_fw_subsumed:                        0
% 2.50/1.00  sim_bw_subsumed:                        0
% 2.50/1.00  sim_fw_subsumption_res:                 0
% 2.50/1.00  sim_bw_subsumption_res:                 0
% 2.50/1.00  sim_tautology_del:                      0
% 2.50/1.00  sim_eq_tautology_del:                   2
% 2.50/1.00  sim_eq_res_simp:                        0
% 2.50/1.00  sim_fw_demodulated:                     2
% 2.50/1.00  sim_bw_demodulated:                     2
% 2.50/1.00  sim_light_normalised:                   11
% 2.50/1.00  sim_joinable_taut:                      0
% 2.50/1.00  sim_joinable_simp:                      0
% 2.50/1.00  sim_ac_normalised:                      0
% 2.50/1.00  sim_smt_subsumption:                    0
% 2.50/1.00  
%------------------------------------------------------------------------------
