%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:37 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 616 expanded)
%              Number of clauses        :   78 ( 148 expanded)
%              Number of leaves         :   23 ( 162 expanded)
%              Depth                    :   22
%              Number of atoms          :  614 (5911 expanded)
%              Number of equality atoms :  100 ( 509 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK8
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK8)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK8) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK7,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK7,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK6)
                      | ~ v3_pre_topc(X3,sK6) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK6)
                        & v3_pre_topc(X3,sK6) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k1_xboole_0 = sK8
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK8)
            | ~ r2_hidden(sK7,X3)
            | ~ v4_pre_topc(X3,sK6)
            | ~ v3_pre_topc(X3,sK6) )
          & ( ( r2_hidden(sK7,X3)
              & v4_pre_topc(X3,sK6)
              & v3_pre_topc(X3,sK6) )
            | ~ r2_hidden(X3,sK8) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
    & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f55,f58,f57,f56])).

fof(f93,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f86,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK8)
      | ~ r2_hidden(sK7,X3)
      | ~ v4_pre_topc(X3,sK6)
      | ~ v3_pre_topc(X3,sK6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    k1_xboole_0 = sK8 ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f37])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
            & r1_tarski(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f39])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v2_tops_1(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v2_tops_1(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f52])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0] :
      ( v2_tops_1(sK5(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1718,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1731,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3344,plain,
    ( r2_hidden(sK7,u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_1731])).

cnf(c_43,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_23,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_26,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_31,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK6)
    | ~ v3_pre_topc(X0,sK6)
    | r2_hidden(X0,sK8)
    | ~ r2_hidden(sK7,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_506,plain,
    ( ~ v3_pre_topc(X0,sK6)
    | r2_hidden(X0,sK8)
    | ~ r2_hidden(sK7,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_struct_0(X1) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_507,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK6),sK6)
    | r2_hidden(k2_struct_0(sK6),sK8)
    | ~ r2_hidden(sK7,k2_struct_0(sK6))
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_509,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK6),sK6)
    | r2_hidden(k2_struct_0(sK6),sK8)
    | ~ r2_hidden(sK7,k2_struct_0(sK6))
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_38,c_37])).

cnf(c_649,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k2_struct_0(sK6),sK8)
    | ~ r2_hidden(sK7,k2_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(sK6) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_509])).

cnf(c_650,plain,
    ( ~ r2_hidden(k2_struct_0(sK6),u1_pre_topc(sK6))
    | r2_hidden(k2_struct_0(sK6),sK8)
    | ~ r2_hidden(sK7,k2_struct_0(sK6))
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_652,plain,
    ( ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK7,k2_struct_0(sK6))
    | r2_hidden(k2_struct_0(sK6),sK8)
    | ~ r2_hidden(k2_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_37])).

cnf(c_653,plain,
    ( ~ r2_hidden(k2_struct_0(sK6),u1_pre_topc(sK6))
    | r2_hidden(k2_struct_0(sK6),sK8)
    | ~ r2_hidden(sK7,k2_struct_0(sK6))
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(renaming,[status(thm)],[c_652])).

cnf(c_1715,plain,
    ( r2_hidden(k2_struct_0(sK6),u1_pre_topc(sK6)) != iProver_top
    | r2_hidden(k2_struct_0(sK6),sK8) = iProver_top
    | r2_hidden(sK7,k2_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 = sK8 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_25,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_22,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_431,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_25,c_22])).

cnf(c_680,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_431,c_37])).

cnf(c_681,plain,
    ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_1817,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) != iProver_top
    | r2_hidden(u1_struct_0(sK6),k1_xboole_0) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1715,c_30,c_681])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1732,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1751,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1732,c_2])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_752,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_753,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_1717,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_21,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_692,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_37])).

cnf(c_693,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ v2_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_82,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_695,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_38,c_37,c_82])).

cnf(c_1713,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_1822,plain,
    ( r2_hidden(sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1817,c_1751,c_1717,c_1713])).

cnf(c_1899,plain,
    ( r2_hidden(sK7,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1900,plain,
    ( r2_hidden(sK7,u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_3532,plain,
    ( v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3344,c_43,c_1822,c_1900])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1733,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3537,plain,
    ( u1_struct_0(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3532,c_1733])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1727,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_28,plain,
    ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_685,plain,
    ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_686,plain,
    ( m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_1714,plain,
    ( m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1730,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2615,plain,
    ( r2_hidden(X0,sK5(sK6)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1730])).

cnf(c_42,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_60,plain,
    ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_62,plain,
    ( m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_1959,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2294,plain,
    ( ~ r2_hidden(X0,sK5(sK6))
    | ~ m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_2295,plain,
    ( r2_hidden(X0,sK5(sK6)) != iProver_top
    | m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2294])).

cnf(c_2633,plain,
    ( r2_hidden(X0,sK5(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2615,c_42,c_43,c_62,c_1822,c_1900,c_2295])).

cnf(c_2640,plain,
    ( sK5(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1727,c_2633])).

cnf(c_27,plain,
    ( v2_tops_1(sK5(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_29,plain,
    ( ~ v2_tops_1(k2_struct_0(X0),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_445,plain,
    ( ~ v2_tops_1(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_39])).

cnf(c_446,plain,
    ( ~ v2_tops_1(k2_struct_0(sK6),sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_58,plain,
    ( ~ v2_tops_1(k2_struct_0(sK6),sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_448,plain,
    ( ~ v2_tops_1(k2_struct_0(sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_39,c_38,c_37,c_58])).

cnf(c_458,plain,
    ( ~ l1_pre_topc(X0)
    | sK5(X0) != k2_struct_0(sK6)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_448])).

cnf(c_459,plain,
    ( ~ l1_pre_topc(sK6)
    | sK5(sK6) != k2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_461,plain,
    ( sK5(sK6) != k2_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_37])).

cnf(c_1744,plain,
    ( sK5(sK6) != u1_struct_0(sK6) ),
    inference(light_normalisation,[status(thm)],[c_461,c_681])).

cnf(c_2937,plain,
    ( u1_struct_0(sK6) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2640,c_1744])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3537,c_2937])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:21:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.06/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/0.98  
% 2.06/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.06/0.98  
% 2.06/0.98  ------  iProver source info
% 2.06/0.98  
% 2.06/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.06/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.06/0.98  git: non_committed_changes: false
% 2.06/0.98  git: last_make_outside_of_git: false
% 2.06/0.98  
% 2.06/0.98  ------ 
% 2.06/0.98  
% 2.06/0.98  ------ Input Options
% 2.06/0.98  
% 2.06/0.98  --out_options                           all
% 2.06/0.98  --tptp_safe_out                         true
% 2.06/0.98  --problem_path                          ""
% 2.06/0.98  --include_path                          ""
% 2.06/0.98  --clausifier                            res/vclausify_rel
% 2.06/0.98  --clausifier_options                    --mode clausify
% 2.06/0.98  --stdin                                 false
% 2.06/0.98  --stats_out                             all
% 2.06/0.98  
% 2.06/0.98  ------ General Options
% 2.06/0.98  
% 2.06/0.98  --fof                                   false
% 2.06/0.98  --time_out_real                         305.
% 2.06/0.98  --time_out_virtual                      -1.
% 2.06/0.98  --symbol_type_check                     false
% 2.06/0.98  --clausify_out                          false
% 2.06/0.98  --sig_cnt_out                           false
% 2.06/0.98  --trig_cnt_out                          false
% 2.06/0.98  --trig_cnt_out_tolerance                1.
% 2.06/0.98  --trig_cnt_out_sk_spl                   false
% 2.06/0.98  --abstr_cl_out                          false
% 2.06/0.98  
% 2.06/0.98  ------ Global Options
% 2.06/0.98  
% 2.06/0.98  --schedule                              default
% 2.06/0.98  --add_important_lit                     false
% 2.06/0.98  --prop_solver_per_cl                    1000
% 2.06/0.98  --min_unsat_core                        false
% 2.06/0.98  --soft_assumptions                      false
% 2.06/0.98  --soft_lemma_size                       3
% 2.06/0.98  --prop_impl_unit_size                   0
% 2.06/0.98  --prop_impl_unit                        []
% 2.06/0.98  --share_sel_clauses                     true
% 2.06/0.98  --reset_solvers                         false
% 2.06/0.98  --bc_imp_inh                            [conj_cone]
% 2.06/0.98  --conj_cone_tolerance                   3.
% 2.06/0.98  --extra_neg_conj                        none
% 2.06/0.98  --large_theory_mode                     true
% 2.06/0.98  --prolific_symb_bound                   200
% 2.06/0.98  --lt_threshold                          2000
% 2.06/0.98  --clause_weak_htbl                      true
% 2.06/0.98  --gc_record_bc_elim                     false
% 2.06/0.98  
% 2.06/0.98  ------ Preprocessing Options
% 2.06/0.98  
% 2.06/0.98  --preprocessing_flag                    true
% 2.06/0.98  --time_out_prep_mult                    0.1
% 2.06/0.98  --splitting_mode                        input
% 2.06/0.98  --splitting_grd                         true
% 2.06/0.98  --splitting_cvd                         false
% 2.06/0.98  --splitting_cvd_svl                     false
% 2.06/0.98  --splitting_nvd                         32
% 2.06/0.98  --sub_typing                            true
% 2.06/0.98  --prep_gs_sim                           true
% 2.06/0.98  --prep_unflatten                        true
% 2.06/0.98  --prep_res_sim                          true
% 2.06/0.98  --prep_upred                            true
% 2.06/0.98  --prep_sem_filter                       exhaustive
% 2.06/0.98  --prep_sem_filter_out                   false
% 2.06/0.98  --pred_elim                             true
% 2.06/0.98  --res_sim_input                         true
% 2.06/0.98  --eq_ax_congr_red                       true
% 2.06/0.98  --pure_diseq_elim                       true
% 2.06/0.98  --brand_transform                       false
% 2.06/0.98  --non_eq_to_eq                          false
% 2.06/0.98  --prep_def_merge                        true
% 2.06/0.98  --prep_def_merge_prop_impl              false
% 2.06/0.98  --prep_def_merge_mbd                    true
% 2.06/0.98  --prep_def_merge_tr_red                 false
% 2.06/0.98  --prep_def_merge_tr_cl                  false
% 2.06/0.98  --smt_preprocessing                     true
% 2.06/0.98  --smt_ac_axioms                         fast
% 2.06/0.98  --preprocessed_out                      false
% 2.06/0.98  --preprocessed_stats                    false
% 2.06/0.98  
% 2.06/0.98  ------ Abstraction refinement Options
% 2.06/0.98  
% 2.06/0.98  --abstr_ref                             []
% 2.06/0.98  --abstr_ref_prep                        false
% 2.06/0.98  --abstr_ref_until_sat                   false
% 2.06/0.98  --abstr_ref_sig_restrict                funpre
% 2.06/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.98  --abstr_ref_under                       []
% 2.06/0.98  
% 2.06/0.98  ------ SAT Options
% 2.06/0.98  
% 2.06/0.98  --sat_mode                              false
% 2.06/0.98  --sat_fm_restart_options                ""
% 2.06/0.98  --sat_gr_def                            false
% 2.06/0.98  --sat_epr_types                         true
% 2.06/0.98  --sat_non_cyclic_types                  false
% 2.06/0.98  --sat_finite_models                     false
% 2.06/0.98  --sat_fm_lemmas                         false
% 2.06/0.98  --sat_fm_prep                           false
% 2.06/0.98  --sat_fm_uc_incr                        true
% 2.06/0.98  --sat_out_model                         small
% 2.06/0.98  --sat_out_clauses                       false
% 2.06/0.98  
% 2.06/0.98  ------ QBF Options
% 2.06/0.98  
% 2.06/0.98  --qbf_mode                              false
% 2.06/0.98  --qbf_elim_univ                         false
% 2.06/0.98  --qbf_dom_inst                          none
% 2.06/0.98  --qbf_dom_pre_inst                      false
% 2.06/0.98  --qbf_sk_in                             false
% 2.06/0.98  --qbf_pred_elim                         true
% 2.06/0.98  --qbf_split                             512
% 2.06/0.98  
% 2.06/0.98  ------ BMC1 Options
% 2.06/0.98  
% 2.06/0.98  --bmc1_incremental                      false
% 2.06/0.98  --bmc1_axioms                           reachable_all
% 2.06/0.98  --bmc1_min_bound                        0
% 2.06/0.98  --bmc1_max_bound                        -1
% 2.06/0.98  --bmc1_max_bound_default                -1
% 2.06/0.98  --bmc1_symbol_reachability              true
% 2.06/0.98  --bmc1_property_lemmas                  false
% 2.06/0.98  --bmc1_k_induction                      false
% 2.06/0.98  --bmc1_non_equiv_states                 false
% 2.06/0.98  --bmc1_deadlock                         false
% 2.06/0.98  --bmc1_ucm                              false
% 2.06/0.98  --bmc1_add_unsat_core                   none
% 2.06/0.98  --bmc1_unsat_core_children              false
% 2.06/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.98  --bmc1_out_stat                         full
% 2.06/0.98  --bmc1_ground_init                      false
% 2.06/0.98  --bmc1_pre_inst_next_state              false
% 2.06/0.98  --bmc1_pre_inst_state                   false
% 2.06/0.98  --bmc1_pre_inst_reach_state             false
% 2.06/0.98  --bmc1_out_unsat_core                   false
% 2.06/0.98  --bmc1_aig_witness_out                  false
% 2.06/0.98  --bmc1_verbose                          false
% 2.06/0.98  --bmc1_dump_clauses_tptp                false
% 2.06/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.98  --bmc1_dump_file                        -
% 2.06/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.98  --bmc1_ucm_extend_mode                  1
% 2.06/0.98  --bmc1_ucm_init_mode                    2
% 2.06/0.98  --bmc1_ucm_cone_mode                    none
% 2.06/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.98  --bmc1_ucm_relax_model                  4
% 2.06/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.98  --bmc1_ucm_layered_model                none
% 2.06/0.98  --bmc1_ucm_max_lemma_size               10
% 2.06/0.98  
% 2.06/0.98  ------ AIG Options
% 2.06/0.98  
% 2.06/0.98  --aig_mode                              false
% 2.06/0.98  
% 2.06/0.98  ------ Instantiation Options
% 2.06/0.98  
% 2.06/0.98  --instantiation_flag                    true
% 2.06/0.98  --inst_sos_flag                         false
% 2.06/0.98  --inst_sos_phase                        true
% 2.06/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.98  --inst_lit_sel_side                     num_symb
% 2.06/0.98  --inst_solver_per_active                1400
% 2.06/0.98  --inst_solver_calls_frac                1.
% 2.06/0.98  --inst_passive_queue_type               priority_queues
% 2.06/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.98  --inst_passive_queues_freq              [25;2]
% 2.06/0.98  --inst_dismatching                      true
% 2.06/0.98  --inst_eager_unprocessed_to_passive     true
% 2.06/0.98  --inst_prop_sim_given                   true
% 2.06/0.98  --inst_prop_sim_new                     false
% 2.06/0.98  --inst_subs_new                         false
% 2.06/0.98  --inst_eq_res_simp                      false
% 2.06/0.98  --inst_subs_given                       false
% 2.06/0.98  --inst_orphan_elimination               true
% 2.06/0.98  --inst_learning_loop_flag               true
% 2.06/0.98  --inst_learning_start                   3000
% 2.06/0.98  --inst_learning_factor                  2
% 2.06/0.98  --inst_start_prop_sim_after_learn       3
% 2.06/0.98  --inst_sel_renew                        solver
% 2.06/0.98  --inst_lit_activity_flag                true
% 2.06/0.98  --inst_restr_to_given                   false
% 2.06/0.98  --inst_activity_threshold               500
% 2.06/0.98  --inst_out_proof                        true
% 2.06/0.98  
% 2.06/0.98  ------ Resolution Options
% 2.06/0.98  
% 2.06/0.98  --resolution_flag                       true
% 2.06/0.98  --res_lit_sel                           adaptive
% 2.06/0.98  --res_lit_sel_side                      none
% 2.06/0.98  --res_ordering                          kbo
% 2.06/0.98  --res_to_prop_solver                    active
% 2.06/0.98  --res_prop_simpl_new                    false
% 2.06/0.98  --res_prop_simpl_given                  true
% 2.06/0.98  --res_passive_queue_type                priority_queues
% 2.06/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.98  --res_passive_queues_freq               [15;5]
% 2.06/0.98  --res_forward_subs                      full
% 2.06/0.98  --res_backward_subs                     full
% 2.06/0.98  --res_forward_subs_resolution           true
% 2.06/0.98  --res_backward_subs_resolution          true
% 2.06/0.98  --res_orphan_elimination                true
% 2.06/0.98  --res_time_limit                        2.
% 2.06/0.98  --res_out_proof                         true
% 2.06/0.98  
% 2.06/0.98  ------ Superposition Options
% 2.06/0.98  
% 2.06/0.98  --superposition_flag                    true
% 2.06/0.98  --sup_passive_queue_type                priority_queues
% 2.06/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.98  --demod_completeness_check              fast
% 2.06/0.98  --demod_use_ground                      true
% 2.06/0.98  --sup_to_prop_solver                    passive
% 2.06/0.98  --sup_prop_simpl_new                    true
% 2.06/0.98  --sup_prop_simpl_given                  true
% 2.06/0.98  --sup_fun_splitting                     false
% 2.06/0.98  --sup_smt_interval                      50000
% 2.06/0.98  
% 2.06/0.98  ------ Superposition Simplification Setup
% 2.06/0.98  
% 2.06/0.98  --sup_indices_passive                   []
% 2.06/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.98  --sup_full_bw                           [BwDemod]
% 2.06/0.98  --sup_immed_triv                        [TrivRules]
% 2.06/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.98  --sup_immed_bw_main                     []
% 2.06/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.98  
% 2.06/0.98  ------ Combination Options
% 2.06/0.98  
% 2.06/0.98  --comb_res_mult                         3
% 2.06/0.98  --comb_sup_mult                         2
% 2.06/0.98  --comb_inst_mult                        10
% 2.06/0.98  
% 2.06/0.98  ------ Debug Options
% 2.06/0.98  
% 2.06/0.98  --dbg_backtrace                         false
% 2.06/0.98  --dbg_dump_prop_clauses                 false
% 2.06/0.98  --dbg_dump_prop_clauses_file            -
% 2.06/0.98  --dbg_out_stat                          false
% 2.06/0.98  ------ Parsing...
% 2.06/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.06/0.98  
% 2.06/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.06/0.98  
% 2.06/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.06/0.98  
% 2.06/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.06/0.98  ------ Proving...
% 2.06/0.98  ------ Problem Properties 
% 2.06/0.98  
% 2.06/0.98  
% 2.06/0.98  clauses                                 27
% 2.06/0.98  conjectures                             4
% 2.06/0.98  EPR                                     5
% 2.06/0.98  Horn                                    21
% 2.06/0.98  unary                                   11
% 2.06/0.98  binary                                  8
% 2.06/0.98  lits                                    55
% 2.06/0.98  lits eq                                 10
% 2.06/0.98  fd_pure                                 0
% 2.06/0.98  fd_pseudo                               0
% 2.06/0.98  fd_cond                                 4
% 2.06/0.98  fd_pseudo_cond                          0
% 2.06/0.98  AC symbols                              0
% 2.06/0.98  
% 2.06/0.98  ------ Schedule dynamic 5 is on 
% 2.06/0.98  
% 2.06/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.06/0.98  
% 2.06/0.98  
% 2.06/0.98  ------ 
% 2.06/0.98  Current options:
% 2.06/0.98  ------ 
% 2.06/0.98  
% 2.06/0.98  ------ Input Options
% 2.06/0.98  
% 2.06/0.98  --out_options                           all
% 2.06/0.98  --tptp_safe_out                         true
% 2.06/0.98  --problem_path                          ""
% 2.06/0.98  --include_path                          ""
% 2.06/0.98  --clausifier                            res/vclausify_rel
% 2.06/0.98  --clausifier_options                    --mode clausify
% 2.06/0.98  --stdin                                 false
% 2.06/0.98  --stats_out                             all
% 2.06/0.98  
% 2.06/0.98  ------ General Options
% 2.06/0.98  
% 2.06/0.98  --fof                                   false
% 2.06/0.98  --time_out_real                         305.
% 2.06/0.98  --time_out_virtual                      -1.
% 2.06/0.98  --symbol_type_check                     false
% 2.06/0.98  --clausify_out                          false
% 2.06/0.98  --sig_cnt_out                           false
% 2.06/0.98  --trig_cnt_out                          false
% 2.06/0.98  --trig_cnt_out_tolerance                1.
% 2.06/0.98  --trig_cnt_out_sk_spl                   false
% 2.06/0.98  --abstr_cl_out                          false
% 2.06/0.98  
% 2.06/0.98  ------ Global Options
% 2.06/0.98  
% 2.06/0.98  --schedule                              default
% 2.06/0.98  --add_important_lit                     false
% 2.06/0.98  --prop_solver_per_cl                    1000
% 2.06/0.98  --min_unsat_core                        false
% 2.06/0.98  --soft_assumptions                      false
% 2.06/0.98  --soft_lemma_size                       3
% 2.06/0.98  --prop_impl_unit_size                   0
% 2.06/0.98  --prop_impl_unit                        []
% 2.06/0.98  --share_sel_clauses                     true
% 2.06/0.98  --reset_solvers                         false
% 2.06/0.98  --bc_imp_inh                            [conj_cone]
% 2.06/0.98  --conj_cone_tolerance                   3.
% 2.06/0.98  --extra_neg_conj                        none
% 2.06/0.98  --large_theory_mode                     true
% 2.06/0.98  --prolific_symb_bound                   200
% 2.06/0.98  --lt_threshold                          2000
% 2.06/0.98  --clause_weak_htbl                      true
% 2.06/0.98  --gc_record_bc_elim                     false
% 2.06/0.98  
% 2.06/0.98  ------ Preprocessing Options
% 2.06/0.98  
% 2.06/0.98  --preprocessing_flag                    true
% 2.06/0.98  --time_out_prep_mult                    0.1
% 2.06/0.98  --splitting_mode                        input
% 2.06/0.98  --splitting_grd                         true
% 2.06/0.98  --splitting_cvd                         false
% 2.06/0.98  --splitting_cvd_svl                     false
% 2.06/0.98  --splitting_nvd                         32
% 2.06/0.98  --sub_typing                            true
% 2.06/0.98  --prep_gs_sim                           true
% 2.06/0.98  --prep_unflatten                        true
% 2.06/0.98  --prep_res_sim                          true
% 2.06/0.98  --prep_upred                            true
% 2.06/0.98  --prep_sem_filter                       exhaustive
% 2.06/0.98  --prep_sem_filter_out                   false
% 2.06/0.98  --pred_elim                             true
% 2.06/0.98  --res_sim_input                         true
% 2.06/0.98  --eq_ax_congr_red                       true
% 2.06/0.98  --pure_diseq_elim                       true
% 2.06/0.98  --brand_transform                       false
% 2.06/0.98  --non_eq_to_eq                          false
% 2.06/0.98  --prep_def_merge                        true
% 2.06/0.98  --prep_def_merge_prop_impl              false
% 2.06/0.98  --prep_def_merge_mbd                    true
% 2.06/0.98  --prep_def_merge_tr_red                 false
% 2.06/0.98  --prep_def_merge_tr_cl                  false
% 2.06/0.98  --smt_preprocessing                     true
% 2.06/0.98  --smt_ac_axioms                         fast
% 2.06/0.98  --preprocessed_out                      false
% 2.06/0.98  --preprocessed_stats                    false
% 2.06/0.98  
% 2.06/0.98  ------ Abstraction refinement Options
% 2.06/0.98  
% 2.06/0.98  --abstr_ref                             []
% 2.06/0.98  --abstr_ref_prep                        false
% 2.06/0.98  --abstr_ref_until_sat                   false
% 2.06/0.98  --abstr_ref_sig_restrict                funpre
% 2.06/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.98  --abstr_ref_under                       []
% 2.06/0.98  
% 2.06/0.98  ------ SAT Options
% 2.06/0.98  
% 2.06/0.98  --sat_mode                              false
% 2.06/0.98  --sat_fm_restart_options                ""
% 2.06/0.98  --sat_gr_def                            false
% 2.06/0.98  --sat_epr_types                         true
% 2.06/0.98  --sat_non_cyclic_types                  false
% 2.06/0.98  --sat_finite_models                     false
% 2.06/0.98  --sat_fm_lemmas                         false
% 2.06/0.98  --sat_fm_prep                           false
% 2.06/0.98  --sat_fm_uc_incr                        true
% 2.06/0.98  --sat_out_model                         small
% 2.06/0.98  --sat_out_clauses                       false
% 2.06/0.98  
% 2.06/0.98  ------ QBF Options
% 2.06/0.98  
% 2.06/0.98  --qbf_mode                              false
% 2.06/0.98  --qbf_elim_univ                         false
% 2.06/0.98  --qbf_dom_inst                          none
% 2.06/0.98  --qbf_dom_pre_inst                      false
% 2.06/0.98  --qbf_sk_in                             false
% 2.06/0.98  --qbf_pred_elim                         true
% 2.06/0.98  --qbf_split                             512
% 2.06/0.98  
% 2.06/0.98  ------ BMC1 Options
% 2.06/0.98  
% 2.06/0.98  --bmc1_incremental                      false
% 2.06/0.98  --bmc1_axioms                           reachable_all
% 2.06/0.98  --bmc1_min_bound                        0
% 2.06/0.98  --bmc1_max_bound                        -1
% 2.06/0.98  --bmc1_max_bound_default                -1
% 2.06/0.98  --bmc1_symbol_reachability              true
% 2.06/0.98  --bmc1_property_lemmas                  false
% 2.06/0.98  --bmc1_k_induction                      false
% 2.06/0.98  --bmc1_non_equiv_states                 false
% 2.06/0.98  --bmc1_deadlock                         false
% 2.06/0.98  --bmc1_ucm                              false
% 2.06/0.98  --bmc1_add_unsat_core                   none
% 2.06/0.98  --bmc1_unsat_core_children              false
% 2.06/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.98  --bmc1_out_stat                         full
% 2.06/0.98  --bmc1_ground_init                      false
% 2.06/0.98  --bmc1_pre_inst_next_state              false
% 2.06/0.98  --bmc1_pre_inst_state                   false
% 2.06/0.98  --bmc1_pre_inst_reach_state             false
% 2.06/0.98  --bmc1_out_unsat_core                   false
% 2.06/0.98  --bmc1_aig_witness_out                  false
% 2.06/0.98  --bmc1_verbose                          false
% 2.06/0.98  --bmc1_dump_clauses_tptp                false
% 2.06/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.98  --bmc1_dump_file                        -
% 2.06/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.98  --bmc1_ucm_extend_mode                  1
% 2.06/0.98  --bmc1_ucm_init_mode                    2
% 2.06/0.98  --bmc1_ucm_cone_mode                    none
% 2.06/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.98  --bmc1_ucm_relax_model                  4
% 2.06/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.98  --bmc1_ucm_layered_model                none
% 2.06/0.98  --bmc1_ucm_max_lemma_size               10
% 2.06/0.98  
% 2.06/0.98  ------ AIG Options
% 2.06/0.98  
% 2.06/0.98  --aig_mode                              false
% 2.06/0.98  
% 2.06/0.98  ------ Instantiation Options
% 2.06/0.98  
% 2.06/0.98  --instantiation_flag                    true
% 2.06/0.98  --inst_sos_flag                         false
% 2.06/0.98  --inst_sos_phase                        true
% 2.06/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.98  --inst_lit_sel_side                     none
% 2.06/0.98  --inst_solver_per_active                1400
% 2.06/0.98  --inst_solver_calls_frac                1.
% 2.06/0.98  --inst_passive_queue_type               priority_queues
% 2.06/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.98  --inst_passive_queues_freq              [25;2]
% 2.06/0.98  --inst_dismatching                      true
% 2.06/0.98  --inst_eager_unprocessed_to_passive     true
% 2.06/0.98  --inst_prop_sim_given                   true
% 2.06/0.98  --inst_prop_sim_new                     false
% 2.06/0.98  --inst_subs_new                         false
% 2.06/0.98  --inst_eq_res_simp                      false
% 2.06/0.98  --inst_subs_given                       false
% 2.06/0.98  --inst_orphan_elimination               true
% 2.06/0.98  --inst_learning_loop_flag               true
% 2.06/0.98  --inst_learning_start                   3000
% 2.06/0.98  --inst_learning_factor                  2
% 2.06/0.98  --inst_start_prop_sim_after_learn       3
% 2.06/0.98  --inst_sel_renew                        solver
% 2.06/0.98  --inst_lit_activity_flag                true
% 2.06/0.98  --inst_restr_to_given                   false
% 2.06/0.98  --inst_activity_threshold               500
% 2.06/0.98  --inst_out_proof                        true
% 2.06/0.98  
% 2.06/0.98  ------ Resolution Options
% 2.06/0.98  
% 2.06/0.98  --resolution_flag                       false
% 2.06/0.98  --res_lit_sel                           adaptive
% 2.06/0.98  --res_lit_sel_side                      none
% 2.06/0.98  --res_ordering                          kbo
% 2.06/0.98  --res_to_prop_solver                    active
% 2.06/0.98  --res_prop_simpl_new                    false
% 2.06/0.98  --res_prop_simpl_given                  true
% 2.06/0.98  --res_passive_queue_type                priority_queues
% 2.06/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.98  --res_passive_queues_freq               [15;5]
% 2.06/0.98  --res_forward_subs                      full
% 2.06/0.98  --res_backward_subs                     full
% 2.06/0.98  --res_forward_subs_resolution           true
% 2.06/0.98  --res_backward_subs_resolution          true
% 2.06/0.98  --res_orphan_elimination                true
% 2.06/0.98  --res_time_limit                        2.
% 2.06/0.98  --res_out_proof                         true
% 2.06/0.98  
% 2.06/0.98  ------ Superposition Options
% 2.06/0.98  
% 2.06/0.98  --superposition_flag                    true
% 2.06/0.98  --sup_passive_queue_type                priority_queues
% 2.06/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.98  --demod_completeness_check              fast
% 2.06/0.98  --demod_use_ground                      true
% 2.06/0.98  --sup_to_prop_solver                    passive
% 2.06/0.98  --sup_prop_simpl_new                    true
% 2.06/0.98  --sup_prop_simpl_given                  true
% 2.06/0.98  --sup_fun_splitting                     false
% 2.06/0.98  --sup_smt_interval                      50000
% 2.06/0.98  
% 2.06/0.98  ------ Superposition Simplification Setup
% 2.06/0.98  
% 2.06/0.98  --sup_indices_passive                   []
% 2.06/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.98  --sup_full_bw                           [BwDemod]
% 2.06/0.98  --sup_immed_triv                        [TrivRules]
% 2.06/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.98  --sup_immed_bw_main                     []
% 2.06/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.98  
% 2.06/0.98  ------ Combination Options
% 2.06/0.98  
% 2.06/0.98  --comb_res_mult                         3
% 2.06/0.98  --comb_sup_mult                         2
% 2.06/0.98  --comb_inst_mult                        10
% 2.06/0.98  
% 2.06/0.98  ------ Debug Options
% 2.06/0.98  
% 2.06/0.98  --dbg_backtrace                         false
% 2.06/0.98  --dbg_dump_prop_clauses                 false
% 2.06/0.98  --dbg_dump_prop_clauses_file            -
% 2.06/0.98  --dbg_out_stat                          false
% 2.06/0.98  
% 2.06/0.98  
% 2.06/0.98  
% 2.06/0.98  
% 2.06/0.98  ------ Proving...
% 2.06/0.98  
% 2.06/0.98  
% 2.06/0.98  % SZS status Theorem for theBenchmark.p
% 2.06/0.98  
% 2.06/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.06/0.98  
% 2.06/0.98  fof(f16,conjecture,(
% 2.06/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 2.06/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.98  
% 2.06/0.98  fof(f17,negated_conjecture,(
% 2.06/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 2.06/0.98    inference(negated_conjecture,[],[f16])).
% 2.06/0.98  
% 2.06/0.98  fof(f35,plain,(
% 2.06/0.98    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.06/0.98    inference(ennf_transformation,[],[f17])).
% 2.06/0.98  
% 2.06/0.98  fof(f36,plain,(
% 2.06/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.98    inference(flattening,[],[f35])).
% 2.06/0.98  
% 2.06/0.98  fof(f54,plain,(
% 2.06/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.98    inference(nnf_transformation,[],[f36])).
% 2.06/0.98  
% 2.06/0.98  fof(f55,plain,(
% 2.06/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.98    inference(flattening,[],[f54])).
% 2.06/0.98  
% 2.06/0.98  fof(f58,plain,(
% 2.06/0.98    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK8 & ! [X3] : (((r2_hidden(X3,sK8) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK8))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.06/0.98    introduced(choice_axiom,[])).
% 2.06/0.98  
% 2.06/0.98  fof(f57,plain,(
% 2.06/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK7,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK7,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 2.06/0.98    introduced(choice_axiom,[])).
% 2.06/0.98  
% 2.06/0.98  fof(f56,plain,(
% 2.06/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK6) | ~v3_pre_topc(X3,sK6)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK6) & v3_pre_topc(X3,sK6)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))) & m1_subset_1(X1,u1_struct_0(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 2.06/0.98    introduced(choice_axiom,[])).
% 2.06/0.98  
% 2.06/0.98  fof(f59,plain,(
% 2.06/0.98    ((k1_xboole_0 = sK8 & ! [X3] : (((r2_hidden(X3,sK8) | ~r2_hidden(sK7,X3) | ~v4_pre_topc(X3,sK6) | ~v3_pre_topc(X3,sK6)) & ((r2_hidden(sK7,X3) & v4_pre_topc(X3,sK6) & v3_pre_topc(X3,sK6)) | ~r2_hidden(X3,sK8))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))) & m1_subset_1(sK7,u1_struct_0(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f55,f58,f57,f56])).
% 2.06/0.99  
% 2.06/0.99  fof(f93,plain,(
% 2.06/0.99    m1_subset_1(sK7,u1_struct_0(sK6))),
% 2.06/0.99    inference(cnf_transformation,[],[f59])).
% 2.06/0.99  
% 2.06/0.99  fof(f5,axiom,(
% 2.06/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f20,plain,(
% 2.06/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.06/0.99    inference(ennf_transformation,[],[f5])).
% 2.06/0.99  
% 2.06/0.99  fof(f21,plain,(
% 2.06/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.06/0.99    inference(flattening,[],[f20])).
% 2.06/0.99  
% 2.06/0.99  fof(f64,plain,(
% 2.06/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f21])).
% 2.06/0.99  
% 2.06/0.99  fof(f11,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f28,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f11])).
% 2.06/0.99  
% 2.06/0.99  fof(f51,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(nnf_transformation,[],[f28])).
% 2.06/0.99  
% 2.06/0.99  fof(f84,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f51])).
% 2.06/0.99  
% 2.06/0.99  fof(f13,axiom,(
% 2.06/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f30,plain,(
% 2.06/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f13])).
% 2.06/0.99  
% 2.06/0.99  fof(f31,plain,(
% 2.06/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.06/0.99    inference(flattening,[],[f30])).
% 2.06/0.99  
% 2.06/0.99  fof(f86,plain,(
% 2.06/0.99    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f31])).
% 2.06/0.99  
% 2.06/0.99  fof(f98,plain,(
% 2.06/0.99    ( ! [X3] : (r2_hidden(X3,sK8) | ~r2_hidden(sK7,X3) | ~v4_pre_topc(X3,sK6) | ~v3_pre_topc(X3,sK6) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f59])).
% 2.06/0.99  
% 2.06/0.99  fof(f91,plain,(
% 2.06/0.99    v2_pre_topc(sK6)),
% 2.06/0.99    inference(cnf_transformation,[],[f59])).
% 2.06/0.99  
% 2.06/0.99  fof(f92,plain,(
% 2.06/0.99    l1_pre_topc(sK6)),
% 2.06/0.99    inference(cnf_transformation,[],[f59])).
% 2.06/0.99  
% 2.06/0.99  fof(f99,plain,(
% 2.06/0.99    k1_xboole_0 = sK8),
% 2.06/0.99    inference(cnf_transformation,[],[f59])).
% 2.06/0.99  
% 2.06/0.99  fof(f12,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f29,plain,(
% 2.06/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f12])).
% 2.06/0.99  
% 2.06/0.99  fof(f85,plain,(
% 2.06/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f29])).
% 2.06/0.99  
% 2.06/0.99  fof(f10,axiom,(
% 2.06/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f27,plain,(
% 2.06/0.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f10])).
% 2.06/0.99  
% 2.06/0.99  fof(f82,plain,(
% 2.06/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f27])).
% 2.06/0.99  
% 2.06/0.99  fof(f4,axiom,(
% 2.06/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f63,plain,(
% 2.06/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f4])).
% 2.06/0.99  
% 2.06/0.99  fof(f3,axiom,(
% 2.06/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f62,plain,(
% 2.06/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.06/0.99    inference(cnf_transformation,[],[f3])).
% 2.06/0.99  
% 2.06/0.99  fof(f2,axiom,(
% 2.06/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f61,plain,(
% 2.06/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f2])).
% 2.06/0.99  
% 2.06/0.99  fof(f7,axiom,(
% 2.06/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f23,plain,(
% 2.06/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.06/0.99    inference(ennf_transformation,[],[f7])).
% 2.06/0.99  
% 2.06/0.99  fof(f66,plain,(
% 2.06/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f23])).
% 2.06/0.99  
% 2.06/0.99  fof(f9,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f18,plain,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.06/0.99    inference(rectify,[],[f9])).
% 2.06/0.99  
% 2.06/0.99  fof(f25,plain,(
% 2.06/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f18])).
% 2.06/0.99  
% 2.06/0.99  fof(f26,plain,(
% 2.06/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(flattening,[],[f25])).
% 2.06/0.99  
% 2.06/0.99  fof(f37,plain,(
% 2.06/0.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.06/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.06/0.99  
% 2.06/0.99  fof(f38,plain,(
% 2.06/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(definition_folding,[],[f26,f37])).
% 2.06/0.99  
% 2.06/0.99  fof(f46,plain,(
% 2.06/0.99    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(nnf_transformation,[],[f38])).
% 2.06/0.99  
% 2.06/0.99  fof(f47,plain,(
% 2.06/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(flattening,[],[f46])).
% 2.06/0.99  
% 2.06/0.99  fof(f48,plain,(
% 2.06/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(rectify,[],[f47])).
% 2.06/0.99  
% 2.06/0.99  fof(f49,plain,(
% 2.06/0.99    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f50,plain,(
% 2.06/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 2.06/0.99  
% 2.06/0.99  fof(f76,plain,(
% 2.06/0.99    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f50])).
% 2.06/0.99  
% 2.06/0.99  fof(f1,axiom,(
% 2.06/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f19,plain,(
% 2.06/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f1])).
% 2.06/0.99  
% 2.06/0.99  fof(f60,plain,(
% 2.06/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f19])).
% 2.06/0.99  
% 2.06/0.99  fof(f8,axiom,(
% 2.06/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f24,plain,(
% 2.06/0.99    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.06/0.99    inference(ennf_transformation,[],[f8])).
% 2.06/0.99  
% 2.06/0.99  fof(f39,plain,(
% 2.06/0.99    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f40,plain,(
% 2.06/0.99    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f39])).
% 2.06/0.99  
% 2.06/0.99  fof(f67,plain,(
% 2.06/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.06/0.99    inference(cnf_transformation,[],[f40])).
% 2.06/0.99  
% 2.06/0.99  fof(f14,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f32,plain,(
% 2.06/0.99    ! [X0] : (? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f14])).
% 2.06/0.99  
% 2.06/0.99  fof(f52,plain,(
% 2.06/0.99    ! [X0] : (? [X1] : (v2_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_1(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f53,plain,(
% 2.06/0.99    ! [X0] : ((v2_tops_1(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f52])).
% 2.06/0.99  
% 2.06/0.99  fof(f87,plain,(
% 2.06/0.99    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f53])).
% 2.06/0.99  
% 2.06/0.99  fof(f6,axiom,(
% 2.06/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f22,plain,(
% 2.06/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.06/0.99    inference(ennf_transformation,[],[f6])).
% 2.06/0.99  
% 2.06/0.99  fof(f65,plain,(
% 2.06/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f22])).
% 2.06/0.99  
% 2.06/0.99  fof(f88,plain,(
% 2.06/0.99    ( ! [X0] : (v2_tops_1(sK5(X0),X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f53])).
% 2.06/0.99  
% 2.06/0.99  fof(f15,axiom,(
% 2.06/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ~v2_tops_1(k2_struct_0(X0),X0))),
% 2.06/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f33,plain,(
% 2.06/0.99    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f15])).
% 2.06/0.99  
% 2.06/0.99  fof(f34,plain,(
% 2.06/0.99    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f33])).
% 2.06/0.99  
% 2.06/0.99  fof(f89,plain,(
% 2.06/0.99    ( ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f34])).
% 2.06/0.99  
% 2.06/0.99  fof(f90,plain,(
% 2.06/0.99    ~v2_struct_0(sK6)),
% 2.06/0.99    inference(cnf_transformation,[],[f59])).
% 2.06/0.99  
% 2.06/0.99  cnf(c_36,negated_conjecture,
% 2.06/0.99      ( m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1718,plain,
% 2.06/0.99      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4,plain,
% 2.06/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1731,plain,
% 2.06/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.06/0.99      | m1_subset_1(X0,X1) != iProver_top
% 2.06/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3344,plain,
% 2.06/0.99      ( r2_hidden(sK7,u1_struct_0(sK6)) = iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_1718,c_1731]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_43,plain,
% 2.06/0.99      ( m1_subset_1(sK7,u1_struct_0(sK6)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_23,plain,
% 2.06/0.99      ( v3_pre_topc(X0,X1)
% 2.06/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_26,plain,
% 2.06/0.99      ( v4_pre_topc(k2_struct_0(X0),X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | ~ v2_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_31,negated_conjecture,
% 2.06/0.99      ( ~ v4_pre_topc(X0,sK6)
% 2.06/0.99      | ~ v3_pre_topc(X0,sK6)
% 2.06/0.99      | r2_hidden(X0,sK8)
% 2.06/0.99      | ~ r2_hidden(sK7,X0)
% 2.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 2.06/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_506,plain,
% 2.06/0.99      ( ~ v3_pre_topc(X0,sK6)
% 2.06/0.99      | r2_hidden(X0,sK8)
% 2.06/0.99      | ~ r2_hidden(sK7,X0)
% 2.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 2.06/0.99      | ~ l1_pre_topc(X1)
% 2.06/0.99      | ~ v2_pre_topc(X1)
% 2.06/0.99      | k2_struct_0(X1) != X0
% 2.06/0.99      | sK6 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_507,plain,
% 2.06/0.99      ( ~ v3_pre_topc(k2_struct_0(sK6),sK6)
% 2.06/0.99      | r2_hidden(k2_struct_0(sK6),sK8)
% 2.06/0.99      | ~ r2_hidden(sK7,k2_struct_0(sK6))
% 2.06/0.99      | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.06/0.99      | ~ l1_pre_topc(sK6)
% 2.06/0.99      | ~ v2_pre_topc(sK6) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_506]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_38,negated_conjecture,
% 2.06/0.99      ( v2_pre_topc(sK6) ),
% 2.06/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_37,negated_conjecture,
% 2.06/0.99      ( l1_pre_topc(sK6) ),
% 2.06/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_509,plain,
% 2.06/0.99      ( ~ v3_pre_topc(k2_struct_0(sK6),sK6)
% 2.06/0.99      | r2_hidden(k2_struct_0(sK6),sK8)
% 2.06/0.99      | ~ r2_hidden(sK7,k2_struct_0(sK6))
% 2.06/0.99      | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_507,c_38,c_37]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_649,plain,
% 2.06/0.99      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.06/0.99      | r2_hidden(k2_struct_0(sK6),sK8)
% 2.06/0.99      | ~ r2_hidden(sK7,k2_struct_0(sK6))
% 2.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.06/0.99      | ~ l1_pre_topc(X1)
% 2.06/0.99      | k2_struct_0(sK6) != X0
% 2.06/0.99      | sK6 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_509]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_650,plain,
% 2.06/0.99      ( ~ r2_hidden(k2_struct_0(sK6),u1_pre_topc(sK6))
% 2.06/0.99      | r2_hidden(k2_struct_0(sK6),sK8)
% 2.06/0.99      | ~ r2_hidden(sK7,k2_struct_0(sK6))
% 2.06/0.99      | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.06/0.99      | ~ l1_pre_topc(sK6) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_649]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_652,plain,
% 2.06/0.99      ( ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.06/0.99      | ~ r2_hidden(sK7,k2_struct_0(sK6))
% 2.06/0.99      | r2_hidden(k2_struct_0(sK6),sK8)
% 2.06/0.99      | ~ r2_hidden(k2_struct_0(sK6),u1_pre_topc(sK6)) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_650,c_37]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_653,plain,
% 2.06/0.99      ( ~ r2_hidden(k2_struct_0(sK6),u1_pre_topc(sK6))
% 2.06/0.99      | r2_hidden(k2_struct_0(sK6),sK8)
% 2.06/0.99      | ~ r2_hidden(sK7,k2_struct_0(sK6))
% 2.06/0.99      | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_652]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1715,plain,
% 2.06/0.99      ( r2_hidden(k2_struct_0(sK6),u1_pre_topc(sK6)) != iProver_top
% 2.06/0.99      | r2_hidden(k2_struct_0(sK6),sK8) = iProver_top
% 2.06/0.99      | r2_hidden(sK7,k2_struct_0(sK6)) != iProver_top
% 2.06/0.99      | m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_30,negated_conjecture,
% 2.06/0.99      ( k1_xboole_0 = sK8 ),
% 2.06/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_25,plain,
% 2.06/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_22,plain,
% 2.06/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_431,plain,
% 2.06/0.99      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 2.06/0.99      inference(resolution,[status(thm)],[c_25,c_22]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_680,plain,
% 2.06/0.99      ( k2_struct_0(X0) = u1_struct_0(X0) | sK6 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_431,c_37]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_681,plain,
% 2.06/0.99      ( k2_struct_0(sK6) = u1_struct_0(sK6) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_680]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1817,plain,
% 2.06/0.99      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) != iProver_top
% 2.06/0.99      | r2_hidden(u1_struct_0(sK6),k1_xboole_0) = iProver_top
% 2.06/0.99      | r2_hidden(sK7,u1_struct_0(sK6)) != iProver_top
% 2.06/0.99      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 2.06/0.99      inference(light_normalisation,[status(thm)],[c_1715,c_30,c_681]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3,plain,
% 2.06/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1732,plain,
% 2.06/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2,plain,
% 2.06/0.99      ( k2_subset_1(X0) = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1751,plain,
% 2.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.06/0.99      inference(light_normalisation,[status(thm)],[c_1732,c_2]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1,plain,
% 2.06/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6,plain,
% 2.06/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_752,plain,
% 2.06/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_6]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_753,plain,
% 2.06/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_752]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1717,plain,
% 2.06/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_21,plain,
% 2.06/0.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | ~ v2_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_692,plain,
% 2.06/0.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.06/0.99      | ~ v2_pre_topc(X0)
% 2.06/0.99      | sK6 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_37]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_693,plain,
% 2.06/0.99      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 2.06/0.99      | ~ v2_pre_topc(sK6) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_692]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_82,plain,
% 2.06/0.99      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 2.06/0.99      | ~ l1_pre_topc(sK6)
% 2.06/0.99      | ~ v2_pre_topc(sK6) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_695,plain,
% 2.06/0.99      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_693,c_38,c_37,c_82]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1713,plain,
% 2.06/0.99      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1822,plain,
% 2.06/0.99      ( r2_hidden(sK7,u1_struct_0(sK6)) != iProver_top ),
% 2.06/0.99      inference(forward_subsumption_resolution,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_1817,c_1751,c_1717,c_1713]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1899,plain,
% 2.06/0.99      ( r2_hidden(sK7,u1_struct_0(sK6))
% 2.06/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK6)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1900,plain,
% 2.06/0.99      ( r2_hidden(sK7,u1_struct_0(sK6)) = iProver_top
% 2.06/0.99      | m1_subset_1(sK7,u1_struct_0(sK6)) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3532,plain,
% 2.06/0.99      ( v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_3344,c_43,c_1822,c_1900]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_0,plain,
% 2.06/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1733,plain,
% 2.06/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3537,plain,
% 2.06/0.99      ( u1_struct_0(sK6) = k1_xboole_0 ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_3532,c_1733]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_9,plain,
% 2.06/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1727,plain,
% 2.06/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_28,plain,
% 2.06/0.99      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.06/0.99      | ~ l1_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_685,plain,
% 2.06/0.99      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK6 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_686,plain,
% 2.06/0.99      ( m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_685]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1714,plain,
% 2.06/0.99      ( m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5,plain,
% 2.06/0.99      ( ~ r2_hidden(X0,X1)
% 2.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.06/0.99      | ~ v1_xboole_0(X2) ),
% 2.06/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1730,plain,
% 2.06/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.06/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 2.06/0.99      | v1_xboole_0(X2) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2615,plain,
% 2.06/0.99      ( r2_hidden(X0,sK5(sK6)) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_1714,c_1730]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_42,plain,
% 2.06/0.99      ( l1_pre_topc(sK6) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_60,plain,
% 2.06/0.99      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_62,plain,
% 2.06/0.99      ( m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_60]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1959,plain,
% 2.06/0.99      ( ~ r2_hidden(X0,X1)
% 2.06/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 2.06/0.99      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2294,plain,
% 2.06/0.99      ( ~ r2_hidden(X0,sK5(sK6))
% 2.06/0.99      | ~ m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 2.06/0.99      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1959]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2295,plain,
% 2.06/0.99      ( r2_hidden(X0,sK5(sK6)) != iProver_top
% 2.06/0.99      | m1_subset_1(sK5(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_2294]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2633,plain,
% 2.06/0.99      ( r2_hidden(X0,sK5(sK6)) != iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_2615,c_42,c_43,c_62,c_1822,c_1900,c_2295]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2640,plain,
% 2.06/0.99      ( sK5(sK6) = k1_xboole_0 ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_1727,c_2633]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_27,plain,
% 2.06/0.99      ( v2_tops_1(sK5(X0),X0) | ~ l1_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_29,plain,
% 2.06/0.99      ( ~ v2_tops_1(k2_struct_0(X0),X0)
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | ~ v2_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_39,negated_conjecture,
% 2.06/0.99      ( ~ v2_struct_0(sK6) ),
% 2.06/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_445,plain,
% 2.06/0.99      ( ~ v2_tops_1(k2_struct_0(X0),X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | ~ v2_pre_topc(X0)
% 2.06/0.99      | sK6 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_39]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_446,plain,
% 2.06/0.99      ( ~ v2_tops_1(k2_struct_0(sK6),sK6)
% 2.06/0.99      | ~ l1_pre_topc(sK6)
% 2.06/0.99      | ~ v2_pre_topc(sK6) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_445]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_58,plain,
% 2.06/0.99      ( ~ v2_tops_1(k2_struct_0(sK6),sK6)
% 2.06/0.99      | v2_struct_0(sK6)
% 2.06/0.99      | ~ l1_pre_topc(sK6)
% 2.06/0.99      | ~ v2_pre_topc(sK6) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_448,plain,
% 2.06/0.99      ( ~ v2_tops_1(k2_struct_0(sK6),sK6) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_446,c_39,c_38,c_37,c_58]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_458,plain,
% 2.06/0.99      ( ~ l1_pre_topc(X0) | sK5(X0) != k2_struct_0(sK6) | sK6 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_448]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_459,plain,
% 2.06/0.99      ( ~ l1_pre_topc(sK6) | sK5(sK6) != k2_struct_0(sK6) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_458]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_461,plain,
% 2.06/0.99      ( sK5(sK6) != k2_struct_0(sK6) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_459,c_37]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1744,plain,
% 2.06/0.99      ( sK5(sK6) != u1_struct_0(sK6) ),
% 2.06/0.99      inference(light_normalisation,[status(thm)],[c_461,c_681]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2937,plain,
% 2.06/0.99      ( u1_struct_0(sK6) != k1_xboole_0 ),
% 2.06/0.99      inference(demodulation,[status(thm)],[c_2640,c_1744]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(contradiction,plain,
% 2.06/0.99      ( $false ),
% 2.06/0.99      inference(minisat,[status(thm)],[c_3537,c_2937]) ).
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  ------                               Statistics
% 2.06/0.99  
% 2.06/0.99  ------ General
% 2.06/0.99  
% 2.06/0.99  abstr_ref_over_cycles:                  0
% 2.06/0.99  abstr_ref_under_cycles:                 0
% 2.06/0.99  gc_basic_clause_elim:                   0
% 2.06/0.99  forced_gc_time:                         0
% 2.06/0.99  parsing_time:                           0.009
% 2.06/0.99  unif_index_cands_time:                  0.
% 2.06/0.99  unif_index_add_time:                    0.
% 2.06/0.99  orderings_time:                         0.
% 2.06/0.99  out_proof_time:                         0.013
% 2.06/0.99  total_time:                             0.124
% 2.06/0.99  num_of_symbols:                         60
% 2.06/0.99  num_of_terms:                           2250
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing
% 2.06/0.99  
% 2.06/0.99  num_of_splits:                          0
% 2.06/0.99  num_of_split_atoms:                     0
% 2.06/0.99  num_of_reused_defs:                     0
% 2.06/0.99  num_eq_ax_congr_red:                    29
% 2.06/0.99  num_of_sem_filtered_clauses:            1
% 2.06/0.99  num_of_subtypes:                        0
% 2.06/0.99  monotx_restored_types:                  0
% 2.06/0.99  sat_num_of_epr_types:                   0
% 2.06/0.99  sat_num_of_non_cyclic_types:            0
% 2.06/0.99  sat_guarded_non_collapsed_types:        0
% 2.06/0.99  num_pure_diseq_elim:                    0
% 2.06/0.99  simp_replaced_by:                       0
% 2.06/0.99  res_preprocessed:                       146
% 2.06/0.99  prep_upred:                             0
% 2.06/0.99  prep_unflattend:                        44
% 2.06/0.99  smt_new_axioms:                         0
% 2.06/0.99  pred_elim_cands:                        4
% 2.06/0.99  pred_elim:                              8
% 2.06/0.99  pred_elim_cl:                           13
% 2.06/0.99  pred_elim_cycles:                       13
% 2.06/0.99  merged_defs:                            0
% 2.06/0.99  merged_defs_ncl:                        0
% 2.06/0.99  bin_hyper_res:                          0
% 2.06/0.99  prep_cycles:                            4
% 2.06/0.99  pred_elim_time:                         0.013
% 2.06/0.99  splitting_time:                         0.
% 2.06/0.99  sem_filter_time:                        0.
% 2.06/0.99  monotx_time:                            0.
% 2.06/0.99  subtype_inf_time:                       0.
% 2.06/0.99  
% 2.06/0.99  ------ Problem properties
% 2.06/0.99  
% 2.06/0.99  clauses:                                27
% 2.06/0.99  conjectures:                            4
% 2.06/0.99  epr:                                    5
% 2.06/0.99  horn:                                   21
% 2.06/0.99  ground:                                 10
% 2.06/0.99  unary:                                  11
% 2.06/0.99  binary:                                 8
% 2.06/0.99  lits:                                   55
% 2.06/0.99  lits_eq:                                10
% 2.06/0.99  fd_pure:                                0
% 2.06/0.99  fd_pseudo:                              0
% 2.06/0.99  fd_cond:                                4
% 2.06/0.99  fd_pseudo_cond:                         0
% 2.06/0.99  ac_symbols:                             0
% 2.06/0.99  
% 2.06/0.99  ------ Propositional Solver
% 2.06/0.99  
% 2.06/0.99  prop_solver_calls:                      25
% 2.06/0.99  prop_fast_solver_calls:                 893
% 2.06/0.99  smt_solver_calls:                       0
% 2.06/0.99  smt_fast_solver_calls:                  0
% 2.06/0.99  prop_num_of_clauses:                    1004
% 2.06/0.99  prop_preprocess_simplified:             4783
% 2.06/0.99  prop_fo_subsumed:                       12
% 2.06/0.99  prop_solver_time:                       0.
% 2.06/0.99  smt_solver_time:                        0.
% 2.06/0.99  smt_fast_solver_time:                   0.
% 2.06/0.99  prop_fast_solver_time:                  0.
% 2.06/0.99  prop_unsat_core_time:                   0.
% 2.06/0.99  
% 2.06/0.99  ------ QBF
% 2.06/0.99  
% 2.06/0.99  qbf_q_res:                              0
% 2.06/0.99  qbf_num_tautologies:                    0
% 2.06/0.99  qbf_prep_cycles:                        0
% 2.06/0.99  
% 2.06/0.99  ------ BMC1
% 2.06/0.99  
% 2.06/0.99  bmc1_current_bound:                     -1
% 2.06/0.99  bmc1_last_solved_bound:                 -1
% 2.06/0.99  bmc1_unsat_core_size:                   -1
% 2.06/0.99  bmc1_unsat_core_parents_size:           -1
% 2.06/0.99  bmc1_merge_next_fun:                    0
% 2.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation
% 2.06/0.99  
% 2.06/0.99  inst_num_of_clauses:                    311
% 2.06/0.99  inst_num_in_passive:                    10
% 2.06/0.99  inst_num_in_active:                     170
% 2.06/0.99  inst_num_in_unprocessed:                131
% 2.06/0.99  inst_num_of_loops:                      180
% 2.06/0.99  inst_num_of_learning_restarts:          0
% 2.06/0.99  inst_num_moves_active_passive:          8
% 2.06/0.99  inst_lit_activity:                      0
% 2.06/0.99  inst_lit_activity_moves:                0
% 2.06/0.99  inst_num_tautologies:                   0
% 2.06/0.99  inst_num_prop_implied:                  0
% 2.06/0.99  inst_num_existing_simplified:           0
% 2.06/0.99  inst_num_eq_res_simplified:             0
% 2.06/0.99  inst_num_child_elim:                    0
% 2.06/0.99  inst_num_of_dismatching_blockings:      46
% 2.06/0.99  inst_num_of_non_proper_insts:           203
% 2.06/0.99  inst_num_of_duplicates:                 0
% 2.06/0.99  inst_inst_num_from_inst_to_res:         0
% 2.06/0.99  inst_dismatching_checking_time:         0.
% 2.06/0.99  
% 2.06/0.99  ------ Resolution
% 2.06/0.99  
% 2.06/0.99  res_num_of_clauses:                     0
% 2.06/0.99  res_num_in_passive:                     0
% 2.06/0.99  res_num_in_active:                      0
% 2.06/0.99  res_num_of_loops:                       150
% 2.06/0.99  res_forward_subset_subsumed:            28
% 2.06/0.99  res_backward_subset_subsumed:           0
% 2.06/0.99  res_forward_subsumed:                   0
% 2.06/0.99  res_backward_subsumed:                  0
% 2.06/0.99  res_forward_subsumption_resolution:     0
% 2.06/0.99  res_backward_subsumption_resolution:    0
% 2.06/0.99  res_clause_to_clause_subsumption:       95
% 2.06/0.99  res_orphan_elimination:                 0
% 2.06/0.99  res_tautology_del:                      25
% 2.06/0.99  res_num_eq_res_simplified:              0
% 2.06/0.99  res_num_sel_changes:                    0
% 2.06/0.99  res_moves_from_active_to_pass:          0
% 2.06/0.99  
% 2.06/0.99  ------ Superposition
% 2.06/0.99  
% 2.06/0.99  sup_time_total:                         0.
% 2.06/0.99  sup_time_generating:                    0.
% 2.06/0.99  sup_time_sim_full:                      0.
% 2.06/0.99  sup_time_sim_immed:                     0.
% 2.06/0.99  
% 2.06/0.99  sup_num_of_clauses:                     42
% 2.06/0.99  sup_num_in_active:                      32
% 2.06/0.99  sup_num_in_passive:                     10
% 2.06/0.99  sup_num_of_loops:                       34
% 2.06/0.99  sup_fw_superposition:                   19
% 2.06/0.99  sup_bw_superposition:                   5
% 2.06/0.99  sup_immediate_simplified:               3
% 2.06/0.99  sup_given_eliminated:                   0
% 2.06/0.99  comparisons_done:                       0
% 2.06/0.99  comparisons_avoided:                    0
% 2.06/0.99  
% 2.06/0.99  ------ Simplifications
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  sim_fw_subset_subsumed:                 2
% 2.06/0.99  sim_bw_subset_subsumed:                 0
% 2.06/0.99  sim_fw_subsumed:                        3
% 2.06/0.99  sim_bw_subsumed:                        0
% 2.06/0.99  sim_fw_subsumption_res:                 4
% 2.06/0.99  sim_bw_subsumption_res:                 0
% 2.06/0.99  sim_tautology_del:                      0
% 2.06/0.99  sim_eq_tautology_del:                   1
% 2.06/0.99  sim_eq_res_simp:                        0
% 2.06/0.99  sim_fw_demodulated:                     0
% 2.06/0.99  sim_bw_demodulated:                     3
% 2.06/0.99  sim_light_normalised:                   6
% 2.06/0.99  sim_joinable_taut:                      0
% 2.06/0.99  sim_joinable_simp:                      0
% 2.06/0.99  sim_ac_normalised:                      0
% 2.06/0.99  sim_smt_subsumption:                    0
% 2.06/0.99  
%------------------------------------------------------------------------------
