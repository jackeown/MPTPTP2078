%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1121+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:55 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  207 (3433 expanded)
%              Number of clauses        :  142 (1010 expanded)
%              Number of leaves         :   18 ( 805 expanded)
%              Depth                    :   23
%              Number of atoms          :  880 (19418 expanded)
%              Number of equality atoms :  276 (4563 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r1_tarski(X1,X3)
                  | ~ v4_pre_topc(X3,X0) )
                & ( ( r1_tarski(X1,X3)
                    & v4_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3(X0,X1))
                | ~ r1_tarski(X1,X3)
                | ~ v4_pre_topc(X3,X0) )
              & ( ( r1_tarski(X1,X3)
                  & v4_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK3(X0,X1)) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
            & ! [X3] :
                ( ( ( r2_hidden(X3,sK3(X0,X1))
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0) )
                  & ( ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,sK3(X0,X1)) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k2_pre_topc(X0,X1) = X1
                  & v2_pre_topc(X0) )
               => v4_pre_topc(X1,X0) )
              & ( v4_pre_topc(X1,X0)
               => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( ~ v4_pre_topc(sK5,X0)
            & k2_pre_topc(X0,sK5) = sK5
            & v2_pre_topc(X0) )
          | ( k2_pre_topc(X0,sK5) != sK5
            & v4_pre_topc(sK5,X0) ) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v4_pre_topc(X1,X0)
                & k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
              | ( k2_pre_topc(X0,X1) != X1
                & v4_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,sK4)
              & k2_pre_topc(sK4,X1) = X1
              & v2_pre_topc(sK4) )
            | ( k2_pre_topc(sK4,X1) != X1
              & v4_pre_topc(X1,sK4) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ( ~ v4_pre_topc(sK5,sK4)
        & k2_pre_topc(sK4,sK5) = sK5
        & v2_pre_topc(sK4) )
      | ( k2_pre_topc(sK4,sK5) != sK5
        & v4_pre_topc(sK5,sK4) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f41,f40])).

fof(f68,plain,
    ( v2_pre_topc(sK4)
    | v4_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,
    ( k2_pre_topc(sK4,sK5) = sK5
    | v4_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK2(X0,X1,X2))
        & r1_tarski(X1,sK2(X0,X1,X2))
        & v4_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK2(X0,X1,X2))
                    & r1_tarski(X1,sK2(X0,X1,X2))
                    & v4_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X2,X4)
      | ~ r1_tarski(X1,X4)
      | ~ v4_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ( ~ v4_pre_topc(sK1(X0,X1),X0)
            & r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,sK3(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,sK3(X0,X1))
      | ~ r1_tarski(X1,X3)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( v4_pre_topc(sK5,sK4)
    | v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_460,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_461,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_465,plain,
    ( m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_30])).

cnf(c_466,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(renaming,[status(thm)],[c_465])).

cnf(c_1608,plain,
    ( v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( ~ v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) != sK5 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( k2_pre_topc(sK4,sK5) != sK5
    | v4_pre_topc(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_467,plain,
    ( v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,k2_pre_topc(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK5,k2_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1851,plain,
    ( ~ r1_tarski(k2_pre_topc(sK4,sK5),sK5)
    | ~ r1_tarski(sK5,k2_pre_topc(sK4,sK5))
    | k2_pre_topc(sK4,sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1877,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1876,plain,
    ( ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),sK5)
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_pre_topc(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_1597,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1615,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1597,c_1615])).

cnf(c_2110,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k2_pre_topc(sK4,X0),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2102])).

cnf(c_2112,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k2_pre_topc(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2110])).

cnf(c_1618,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1612,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_650,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_651,plain,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK4,X1))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_1601,plain,
    ( v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(X2,k2_pre_topc(sK4,X1)) != iProver_top
    | r2_hidden(X2,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_1901,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK4,X0)) != iProver_top
    | r2_hidden(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_1601])).

cnf(c_2335,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_1901])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_96,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_98,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_2381,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
    | v4_pre_topc(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2335,c_98])).

cnf(c_2382,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_2381])).

cnf(c_2391,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),sK5) = iProver_top
    | r1_tarski(k2_pre_topc(sK4,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1618,c_2382])).

cnf(c_2392,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),u1_struct_0(sK4))
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),sK5)
    | r1_tarski(k2_pre_topc(sK4,sK5),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2391])).

cnf(c_2394,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4))
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),sK5)
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1967,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),X0)
    | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | ~ r1_tarski(k2_pre_topc(sK4,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2422,plain,
    ( ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4))
    | ~ r1_tarski(k2_pre_topc(sK4,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_2519,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1608,c_29,c_26,c_37,c_467,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_11,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_388,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_389,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_393,plain,
    ( m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_30])).

cnf(c_394,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_1611,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_31,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_390,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_3034,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1611,c_31,c_29,c_26,c_37,c_390,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_3043,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(sK1(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_1615])).

cnf(c_6368,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK1(sK4,sK3(sK4,X0)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2519,c_3043])).

cnf(c_6385,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK1(sK4,sK3(sK4,sK5)),u1_struct_0(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6368])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1616,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_412,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_413,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,X0),X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( r2_hidden(sK1(sK4,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_30])).

cnf(c_418,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,X0),X0) ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_1610,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_414,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_2532,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1610,c_31,c_29,c_26,c_37,c_414,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_2541,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_2532])).

cnf(c_20,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,sK3(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_481,plain,
    ( v4_pre_topc(X0,X1)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,sK3(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_482,plain,
    ( v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK3(sK4,X1))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,sK3(sK4,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_30])).

cnf(c_487,plain,
    ( v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_486])).

cnf(c_1607,plain,
    ( v4_pre_topc(X0,sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK3(sK4,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_488,plain,
    ( v4_pre_topc(X0,sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK3(sK4,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_3361,plain,
    ( v4_pre_topc(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK3(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_29,c_26,c_37,c_488,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_3369,plain,
    ( v4_pre_topc(X0,sK4) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK3(sK4,X1)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_3361])).

cnf(c_5157,plain,
    ( v4_pre_topc(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3(sK4,sK5)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_3369])).

cnf(c_5648,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,sK5)),sK4) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4) = iProver_top
    | r1_tarski(sK3(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK1(sK4,sK3(sK4,sK5)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_5157])).

cnf(c_1602,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_1849,plain,
    ( r1_tarski(sK5,k2_pre_topc(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_1602])).

cnf(c_1621,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2853,plain,
    ( k2_pre_topc(sK4,sK5) = sK5
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1621])).

cnf(c_3672,plain,
    ( k2_pre_topc(sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2853,c_29,c_26,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_557,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_558,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4)
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_30])).

cnf(c_563,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_1604,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_559,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_2471,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1604,c_31,c_29,c_26,c_37,c_559,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_2480,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = k2_pre_topc(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1612,c_2471])).

cnf(c_3675,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_3672,c_2480])).

cnf(c_5663,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,sK5)),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | r1_tarski(sK3(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK1(sK4,sK3(sK4,sK5)),u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5648,c_3675])).

cnf(c_1005,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5514,plain,
    ( X0 != X1
    | X0 = k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X2))
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_5515,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) != sK5
    | sK5 = k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5514])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_436,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_437,plain,
    ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | ~ v4_pre_topc(sK1(sK4,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_30])).

cnf(c_442,plain,
    ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_1609,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_443,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_3004,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1609,c_29,c_26,c_37,c_443,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_3005,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3004])).

cnf(c_3013,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1616,c_3005])).

cnf(c_4676,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,sK5)),sK4) != iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | r1_tarski(sK3(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3675,c_3013])).

cnf(c_18,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,sK3(X1,X2))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_531,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,sK3(X1,X2))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_532,plain,
    ( ~ v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK3(sK4,X1))
    | ~ r1_tarski(X1,X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( ~ r1_tarski(X1,X0)
    | r2_hidden(X0,sK3(sK4,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4)
    | ~ v4_pre_topc(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_30])).

cnf(c_535,plain,
    ( ~ v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK3(sK4,X1))
    | ~ r1_tarski(X1,X0) ),
    inference(renaming,[status(thm)],[c_534])).

cnf(c_1605,plain,
    ( v4_pre_topc(X0,sK4) != iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK3(sK4,X1)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_533,plain,
    ( v4_pre_topc(X0,sK4) != iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK3(sK4,X1)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_3560,plain,
    ( v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK3(sK4,X1)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1605,c_31,c_29,c_26,c_37,c_533,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_3563,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK5,sK3(sK4,sK5)) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3560])).

cnf(c_1013,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2018,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,sK4)
    | X0 != X2
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_2294,plain,
    ( ~ v4_pre_topc(X0,sK4)
    | v4_pre_topc(X1,sK4)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_3490,plain,
    ( v4_pre_topc(X0,sK4)
    | ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X1)),sK4)
    | X0 != k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X1))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2294])).

cnf(c_3491,plain,
    ( X0 != k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X1))
    | sK4 != sK4
    | v4_pre_topc(X0,sK4) = iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X1)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3490])).

cnf(c_3493,plain,
    ( sK4 != sK4
    | sK5 != k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)),sK4) != iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3491])).

cnf(c_3370,plain,
    ( v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK5,sK3(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_3361])).

cnf(c_3422,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK5,sK3(sK4,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3370,c_29,c_26,c_37,c_641,c_1851,c_1877,c_1876,c_2112,c_2394,c_2422])).

cnf(c_3425,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK5,sK3(sK4,sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3422])).

cnf(c_2527,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK3(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2519,c_1615])).

cnf(c_2529,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK3(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_1004,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1947,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_101,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_97,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6385,c_5663,c_5515,c_4676,c_3675,c_3563,c_3493,c_3425,c_2529,c_1947,c_101,c_98,c_97,c_32])).


%------------------------------------------------------------------------------
