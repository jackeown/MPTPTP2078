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
% DateTime   : Thu Dec  3 12:18:38 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 278 expanded)
%              Number of clauses        :   64 (  85 expanded)
%              Number of leaves         :   20 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  558 (2292 expanded)
%              Number of equality atoms :   94 ( 242 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f54,plain,(
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
     => ( k1_xboole_0 = sK6
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK6)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK6) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
                    | ~ r2_hidden(sK5,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK5,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
                      | ~ v4_pre_topc(X3,sK4)
                      | ~ v3_pre_topc(X3,sK4) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK4)
                        & v3_pre_topc(X3,sK4) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k1_xboole_0 = sK6
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK6)
            | ~ r2_hidden(sK5,X3)
            | ~ v4_pre_topc(X3,sK4)
            | ~ v3_pre_topc(X3,sK4) )
          & ( ( r2_hidden(sK5,X3)
              & v4_pre_topc(X3,sK4)
              & v3_pre_topc(X3,sK4) )
            | ~ r2_hidden(X3,sK6) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f54,f53,f52])).

fof(f92,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK6)
      | ~ r2_hidden(sK5,X3)
      | ~ v4_pre_topc(X3,sK4)
      | ~ v3_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    k1_xboole_0 = sK6 ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(rectify,[],[f10])).

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

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f36])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1678,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1680,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2468,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1678,c_1680])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2473,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2468,c_1])).

cnf(c_27,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ v3_pre_topc(X0,sK4)
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_527,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | r2_hidden(X2,sK6)
    | ~ r2_hidden(sK5,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),X0) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_528,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4)
    | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),sK6)
    | ~ r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_532,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0))
    | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),sK6)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4)
    | ~ v3_pre_topc(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_35])).

cnf(c_533,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4)
    | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),sK6)
    | ~ r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_532])).

cnf(c_1664,plain,
    ( v3_pre_topc(X0,sK4) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),sK6) = iProver_top
    | r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 = sK6 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1766,plain,
    ( v3_pre_topc(X0,sK4) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4) != iProver_top
    | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1664,c_28])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_701,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_702,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_1665,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_1773,plain,
    ( v3_pre_topc(X0,sK4) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4) != iProver_top
    | r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1766,c_1665])).

cnf(c_2478,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK4),k1_xboole_0),sK4) != iProver_top
    | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
    | r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),k1_xboole_0)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2473,c_1773])).

cnf(c_2479,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK4) != iProver_top
    | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2478,c_2473])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_39,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_61,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_63,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_20,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_76,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_78,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_21,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_668,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_669,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X0,u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_1831,plain,
    ( v3_pre_topc(k1_xboole_0,sK4)
    | ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK4))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1832,plain,
    ( v3_pre_topc(k1_xboole_0,sK4) = iProver_top
    | r2_hidden(k1_xboole_0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1831])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_400,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_37])).

cnf(c_401,plain,
    ( ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_65,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_68,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_403,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_37,c_35,c_65,c_68])).

cnf(c_413,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_403])).

cnf(c_414,plain,
    ( r2_hidden(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_1843,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_1844,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1843])).

cnf(c_1846,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1848,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1846])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1679,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1699,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1679,c_2])).

cnf(c_1658,plain,
    ( v3_pre_topc(X0,sK4) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_2168,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1658])).

cnf(c_2629,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2479,c_39,c_40,c_41,c_63,c_78,c_1832,c_1844,c_1848,c_2168])).

cnf(c_2634,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2629,c_1699])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:39:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 1.92/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/0.99  
% 1.92/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.92/0.99  
% 1.92/0.99  ------  iProver source info
% 1.92/0.99  
% 1.92/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.92/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.92/0.99  git: non_committed_changes: false
% 1.92/0.99  git: last_make_outside_of_git: false
% 1.92/0.99  
% 1.92/0.99  ------ 
% 1.92/0.99  
% 1.92/0.99  ------ Input Options
% 1.92/0.99  
% 1.92/0.99  --out_options                           all
% 1.92/0.99  --tptp_safe_out                         true
% 1.92/0.99  --problem_path                          ""
% 1.92/0.99  --include_path                          ""
% 1.92/0.99  --clausifier                            res/vclausify_rel
% 1.92/0.99  --clausifier_options                    --mode clausify
% 1.92/0.99  --stdin                                 false
% 1.92/0.99  --stats_out                             all
% 1.92/0.99  
% 1.92/0.99  ------ General Options
% 1.92/0.99  
% 1.92/0.99  --fof                                   false
% 1.92/0.99  --time_out_real                         305.
% 1.92/0.99  --time_out_virtual                      -1.
% 1.92/0.99  --symbol_type_check                     false
% 1.92/0.99  --clausify_out                          false
% 1.92/0.99  --sig_cnt_out                           false
% 1.92/0.99  --trig_cnt_out                          false
% 1.92/0.99  --trig_cnt_out_tolerance                1.
% 1.92/0.99  --trig_cnt_out_sk_spl                   false
% 1.92/0.99  --abstr_cl_out                          false
% 1.92/0.99  
% 1.92/0.99  ------ Global Options
% 1.92/0.99  
% 1.92/0.99  --schedule                              default
% 1.92/0.99  --add_important_lit                     false
% 1.92/0.99  --prop_solver_per_cl                    1000
% 1.92/0.99  --min_unsat_core                        false
% 1.92/0.99  --soft_assumptions                      false
% 1.92/0.99  --soft_lemma_size                       3
% 1.92/0.99  --prop_impl_unit_size                   0
% 1.92/0.99  --prop_impl_unit                        []
% 1.92/0.99  --share_sel_clauses                     true
% 1.92/0.99  --reset_solvers                         false
% 1.92/0.99  --bc_imp_inh                            [conj_cone]
% 1.92/0.99  --conj_cone_tolerance                   3.
% 1.92/0.99  --extra_neg_conj                        none
% 1.92/0.99  --large_theory_mode                     true
% 1.92/0.99  --prolific_symb_bound                   200
% 1.92/0.99  --lt_threshold                          2000
% 1.92/0.99  --clause_weak_htbl                      true
% 1.92/0.99  --gc_record_bc_elim                     false
% 1.92/0.99  
% 1.92/0.99  ------ Preprocessing Options
% 1.92/0.99  
% 1.92/0.99  --preprocessing_flag                    true
% 1.92/0.99  --time_out_prep_mult                    0.1
% 1.92/0.99  --splitting_mode                        input
% 1.92/0.99  --splitting_grd                         true
% 1.92/0.99  --splitting_cvd                         false
% 1.92/0.99  --splitting_cvd_svl                     false
% 1.92/0.99  --splitting_nvd                         32
% 1.92/0.99  --sub_typing                            true
% 1.92/0.99  --prep_gs_sim                           true
% 1.92/0.99  --prep_unflatten                        true
% 1.92/0.99  --prep_res_sim                          true
% 1.92/0.99  --prep_upred                            true
% 1.92/0.99  --prep_sem_filter                       exhaustive
% 1.92/0.99  --prep_sem_filter_out                   false
% 1.92/0.99  --pred_elim                             true
% 1.92/0.99  --res_sim_input                         true
% 1.92/0.99  --eq_ax_congr_red                       true
% 1.92/0.99  --pure_diseq_elim                       true
% 1.92/0.99  --brand_transform                       false
% 1.92/0.99  --non_eq_to_eq                          false
% 1.92/0.99  --prep_def_merge                        true
% 1.92/0.99  --prep_def_merge_prop_impl              false
% 1.92/0.99  --prep_def_merge_mbd                    true
% 1.92/0.99  --prep_def_merge_tr_red                 false
% 1.92/0.99  --prep_def_merge_tr_cl                  false
% 1.92/0.99  --smt_preprocessing                     true
% 1.92/0.99  --smt_ac_axioms                         fast
% 1.92/0.99  --preprocessed_out                      false
% 1.92/0.99  --preprocessed_stats                    false
% 1.92/0.99  
% 1.92/0.99  ------ Abstraction refinement Options
% 1.92/0.99  
% 1.92/0.99  --abstr_ref                             []
% 1.92/0.99  --abstr_ref_prep                        false
% 1.92/0.99  --abstr_ref_until_sat                   false
% 1.92/0.99  --abstr_ref_sig_restrict                funpre
% 1.92/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/0.99  --abstr_ref_under                       []
% 1.92/0.99  
% 1.92/0.99  ------ SAT Options
% 1.92/0.99  
% 1.92/0.99  --sat_mode                              false
% 1.92/0.99  --sat_fm_restart_options                ""
% 1.92/0.99  --sat_gr_def                            false
% 1.92/0.99  --sat_epr_types                         true
% 1.92/0.99  --sat_non_cyclic_types                  false
% 1.92/0.99  --sat_finite_models                     false
% 1.92/0.99  --sat_fm_lemmas                         false
% 1.92/0.99  --sat_fm_prep                           false
% 1.92/0.99  --sat_fm_uc_incr                        true
% 1.92/0.99  --sat_out_model                         small
% 1.92/0.99  --sat_out_clauses                       false
% 1.92/0.99  
% 1.92/0.99  ------ QBF Options
% 1.92/0.99  
% 1.92/0.99  --qbf_mode                              false
% 1.92/0.99  --qbf_elim_univ                         false
% 1.92/0.99  --qbf_dom_inst                          none
% 1.92/0.99  --qbf_dom_pre_inst                      false
% 1.92/0.99  --qbf_sk_in                             false
% 1.92/0.99  --qbf_pred_elim                         true
% 1.92/0.99  --qbf_split                             512
% 1.92/0.99  
% 1.92/0.99  ------ BMC1 Options
% 1.92/0.99  
% 1.92/0.99  --bmc1_incremental                      false
% 1.92/0.99  --bmc1_axioms                           reachable_all
% 1.92/0.99  --bmc1_min_bound                        0
% 1.92/0.99  --bmc1_max_bound                        -1
% 1.92/0.99  --bmc1_max_bound_default                -1
% 1.92/0.99  --bmc1_symbol_reachability              true
% 1.92/0.99  --bmc1_property_lemmas                  false
% 1.92/0.99  --bmc1_k_induction                      false
% 1.92/0.99  --bmc1_non_equiv_states                 false
% 1.92/0.99  --bmc1_deadlock                         false
% 1.92/0.99  --bmc1_ucm                              false
% 1.92/0.99  --bmc1_add_unsat_core                   none
% 1.92/0.99  --bmc1_unsat_core_children              false
% 1.92/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/0.99  --bmc1_out_stat                         full
% 1.92/0.99  --bmc1_ground_init                      false
% 1.92/0.99  --bmc1_pre_inst_next_state              false
% 1.92/0.99  --bmc1_pre_inst_state                   false
% 1.92/0.99  --bmc1_pre_inst_reach_state             false
% 1.92/0.99  --bmc1_out_unsat_core                   false
% 1.92/0.99  --bmc1_aig_witness_out                  false
% 1.92/0.99  --bmc1_verbose                          false
% 1.92/0.99  --bmc1_dump_clauses_tptp                false
% 1.92/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.92/0.99  --bmc1_dump_file                        -
% 1.92/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.92/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.92/0.99  --bmc1_ucm_extend_mode                  1
% 1.92/0.99  --bmc1_ucm_init_mode                    2
% 1.92/0.99  --bmc1_ucm_cone_mode                    none
% 1.92/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.92/0.99  --bmc1_ucm_relax_model                  4
% 1.92/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.92/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/0.99  --bmc1_ucm_layered_model                none
% 1.92/0.99  --bmc1_ucm_max_lemma_size               10
% 1.92/0.99  
% 1.92/0.99  ------ AIG Options
% 1.92/0.99  
% 1.92/0.99  --aig_mode                              false
% 1.92/0.99  
% 1.92/0.99  ------ Instantiation Options
% 1.92/0.99  
% 1.92/0.99  --instantiation_flag                    true
% 1.92/0.99  --inst_sos_flag                         false
% 1.92/0.99  --inst_sos_phase                        true
% 1.92/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/0.99  --inst_lit_sel_side                     num_symb
% 1.92/0.99  --inst_solver_per_active                1400
% 1.92/0.99  --inst_solver_calls_frac                1.
% 1.92/0.99  --inst_passive_queue_type               priority_queues
% 1.92/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/0.99  --inst_passive_queues_freq              [25;2]
% 1.92/0.99  --inst_dismatching                      true
% 1.92/0.99  --inst_eager_unprocessed_to_passive     true
% 1.92/0.99  --inst_prop_sim_given                   true
% 1.92/0.99  --inst_prop_sim_new                     false
% 1.92/0.99  --inst_subs_new                         false
% 1.92/1.00  --inst_eq_res_simp                      false
% 1.92/1.00  --inst_subs_given                       false
% 1.92/1.00  --inst_orphan_elimination               true
% 1.92/1.00  --inst_learning_loop_flag               true
% 1.92/1.00  --inst_learning_start                   3000
% 1.92/1.00  --inst_learning_factor                  2
% 1.92/1.00  --inst_start_prop_sim_after_learn       3
% 1.92/1.00  --inst_sel_renew                        solver
% 1.92/1.00  --inst_lit_activity_flag                true
% 1.92/1.00  --inst_restr_to_given                   false
% 1.92/1.00  --inst_activity_threshold               500
% 1.92/1.00  --inst_out_proof                        true
% 1.92/1.00  
% 1.92/1.00  ------ Resolution Options
% 1.92/1.00  
% 1.92/1.00  --resolution_flag                       true
% 1.92/1.00  --res_lit_sel                           adaptive
% 1.92/1.00  --res_lit_sel_side                      none
% 1.92/1.00  --res_ordering                          kbo
% 1.92/1.00  --res_to_prop_solver                    active
% 1.92/1.00  --res_prop_simpl_new                    false
% 1.92/1.00  --res_prop_simpl_given                  true
% 1.92/1.00  --res_passive_queue_type                priority_queues
% 1.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/1.00  --res_passive_queues_freq               [15;5]
% 1.92/1.00  --res_forward_subs                      full
% 1.92/1.00  --res_backward_subs                     full
% 1.92/1.00  --res_forward_subs_resolution           true
% 1.92/1.00  --res_backward_subs_resolution          true
% 1.92/1.00  --res_orphan_elimination                true
% 1.92/1.00  --res_time_limit                        2.
% 1.92/1.00  --res_out_proof                         true
% 1.92/1.00  
% 1.92/1.00  ------ Superposition Options
% 1.92/1.00  
% 1.92/1.00  --superposition_flag                    true
% 1.92/1.00  --sup_passive_queue_type                priority_queues
% 1.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.92/1.00  --demod_completeness_check              fast
% 1.92/1.00  --demod_use_ground                      true
% 1.92/1.00  --sup_to_prop_solver                    passive
% 1.92/1.00  --sup_prop_simpl_new                    true
% 1.92/1.00  --sup_prop_simpl_given                  true
% 1.92/1.00  --sup_fun_splitting                     false
% 1.92/1.00  --sup_smt_interval                      50000
% 1.92/1.00  
% 1.92/1.00  ------ Superposition Simplification Setup
% 1.92/1.00  
% 1.92/1.00  --sup_indices_passive                   []
% 1.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.00  --sup_full_bw                           [BwDemod]
% 1.92/1.00  --sup_immed_triv                        [TrivRules]
% 1.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.00  --sup_immed_bw_main                     []
% 1.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.00  
% 1.92/1.00  ------ Combination Options
% 1.92/1.00  
% 1.92/1.00  --comb_res_mult                         3
% 1.92/1.00  --comb_sup_mult                         2
% 1.92/1.00  --comb_inst_mult                        10
% 1.92/1.00  
% 1.92/1.00  ------ Debug Options
% 1.92/1.00  
% 1.92/1.00  --dbg_backtrace                         false
% 1.92/1.00  --dbg_dump_prop_clauses                 false
% 1.92/1.00  --dbg_dump_prop_clauses_file            -
% 1.92/1.00  --dbg_out_stat                          false
% 1.92/1.00  ------ Parsing...
% 1.92/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.92/1.00  
% 1.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.92/1.00  
% 1.92/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.92/1.00  
% 1.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.92/1.00  ------ Proving...
% 1.92/1.00  ------ Problem Properties 
% 1.92/1.00  
% 1.92/1.00  
% 1.92/1.00  clauses                                 27
% 1.92/1.00  conjectures                             5
% 1.92/1.00  EPR                                     3
% 1.92/1.00  Horn                                    23
% 1.92/1.00  unary                                   12
% 1.92/1.00  binary                                  7
% 1.92/1.00  lits                                    57
% 1.92/1.00  lits eq                                 4
% 1.92/1.00  fd_pure                                 0
% 1.92/1.00  fd_pseudo                               0
% 1.92/1.00  fd_cond                                 0
% 1.92/1.00  fd_pseudo_cond                          0
% 1.92/1.00  AC symbols                              0
% 1.92/1.00  
% 1.92/1.00  ------ Schedule dynamic 5 is on 
% 1.92/1.00  
% 1.92/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.92/1.00  
% 1.92/1.00  
% 1.92/1.00  ------ 
% 1.92/1.00  Current options:
% 1.92/1.00  ------ 
% 1.92/1.00  
% 1.92/1.00  ------ Input Options
% 1.92/1.00  
% 1.92/1.00  --out_options                           all
% 1.92/1.00  --tptp_safe_out                         true
% 1.92/1.00  --problem_path                          ""
% 1.92/1.00  --include_path                          ""
% 1.92/1.00  --clausifier                            res/vclausify_rel
% 1.92/1.00  --clausifier_options                    --mode clausify
% 1.92/1.00  --stdin                                 false
% 1.92/1.00  --stats_out                             all
% 1.92/1.00  
% 1.92/1.00  ------ General Options
% 1.92/1.00  
% 1.92/1.00  --fof                                   false
% 1.92/1.00  --time_out_real                         305.
% 1.92/1.00  --time_out_virtual                      -1.
% 1.92/1.00  --symbol_type_check                     false
% 1.92/1.00  --clausify_out                          false
% 1.92/1.00  --sig_cnt_out                           false
% 1.92/1.00  --trig_cnt_out                          false
% 1.92/1.00  --trig_cnt_out_tolerance                1.
% 1.92/1.00  --trig_cnt_out_sk_spl                   false
% 1.92/1.00  --abstr_cl_out                          false
% 1.92/1.00  
% 1.92/1.00  ------ Global Options
% 1.92/1.00  
% 1.92/1.00  --schedule                              default
% 1.92/1.00  --add_important_lit                     false
% 1.92/1.00  --prop_solver_per_cl                    1000
% 1.92/1.00  --min_unsat_core                        false
% 1.92/1.00  --soft_assumptions                      false
% 1.92/1.00  --soft_lemma_size                       3
% 1.92/1.00  --prop_impl_unit_size                   0
% 1.92/1.00  --prop_impl_unit                        []
% 1.92/1.00  --share_sel_clauses                     true
% 1.92/1.00  --reset_solvers                         false
% 1.92/1.00  --bc_imp_inh                            [conj_cone]
% 1.92/1.00  --conj_cone_tolerance                   3.
% 1.92/1.00  --extra_neg_conj                        none
% 1.92/1.00  --large_theory_mode                     true
% 1.92/1.00  --prolific_symb_bound                   200
% 1.92/1.00  --lt_threshold                          2000
% 1.92/1.00  --clause_weak_htbl                      true
% 1.92/1.00  --gc_record_bc_elim                     false
% 1.92/1.00  
% 1.92/1.00  ------ Preprocessing Options
% 1.92/1.00  
% 1.92/1.00  --preprocessing_flag                    true
% 1.92/1.00  --time_out_prep_mult                    0.1
% 1.92/1.00  --splitting_mode                        input
% 1.92/1.00  --splitting_grd                         true
% 1.92/1.00  --splitting_cvd                         false
% 1.92/1.00  --splitting_cvd_svl                     false
% 1.92/1.00  --splitting_nvd                         32
% 1.92/1.00  --sub_typing                            true
% 1.92/1.00  --prep_gs_sim                           true
% 1.92/1.00  --prep_unflatten                        true
% 1.92/1.00  --prep_res_sim                          true
% 1.92/1.00  --prep_upred                            true
% 1.92/1.00  --prep_sem_filter                       exhaustive
% 1.92/1.00  --prep_sem_filter_out                   false
% 1.92/1.00  --pred_elim                             true
% 1.92/1.00  --res_sim_input                         true
% 1.92/1.00  --eq_ax_congr_red                       true
% 1.92/1.00  --pure_diseq_elim                       true
% 1.92/1.00  --brand_transform                       false
% 1.92/1.00  --non_eq_to_eq                          false
% 1.92/1.00  --prep_def_merge                        true
% 1.92/1.00  --prep_def_merge_prop_impl              false
% 1.92/1.00  --prep_def_merge_mbd                    true
% 1.92/1.00  --prep_def_merge_tr_red                 false
% 1.92/1.00  --prep_def_merge_tr_cl                  false
% 1.92/1.00  --smt_preprocessing                     true
% 1.92/1.00  --smt_ac_axioms                         fast
% 1.92/1.00  --preprocessed_out                      false
% 1.92/1.00  --preprocessed_stats                    false
% 1.92/1.00  
% 1.92/1.00  ------ Abstraction refinement Options
% 1.92/1.00  
% 1.92/1.00  --abstr_ref                             []
% 1.92/1.00  --abstr_ref_prep                        false
% 1.92/1.00  --abstr_ref_until_sat                   false
% 1.92/1.00  --abstr_ref_sig_restrict                funpre
% 1.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/1.00  --abstr_ref_under                       []
% 1.92/1.00  
% 1.92/1.00  ------ SAT Options
% 1.92/1.00  
% 1.92/1.00  --sat_mode                              false
% 1.92/1.00  --sat_fm_restart_options                ""
% 1.92/1.00  --sat_gr_def                            false
% 1.92/1.00  --sat_epr_types                         true
% 1.92/1.00  --sat_non_cyclic_types                  false
% 1.92/1.00  --sat_finite_models                     false
% 1.92/1.00  --sat_fm_lemmas                         false
% 1.92/1.00  --sat_fm_prep                           false
% 1.92/1.00  --sat_fm_uc_incr                        true
% 1.92/1.00  --sat_out_model                         small
% 1.92/1.00  --sat_out_clauses                       false
% 1.92/1.00  
% 1.92/1.00  ------ QBF Options
% 1.92/1.00  
% 1.92/1.00  --qbf_mode                              false
% 1.92/1.00  --qbf_elim_univ                         false
% 1.92/1.00  --qbf_dom_inst                          none
% 1.92/1.00  --qbf_dom_pre_inst                      false
% 1.92/1.00  --qbf_sk_in                             false
% 1.92/1.00  --qbf_pred_elim                         true
% 1.92/1.00  --qbf_split                             512
% 1.92/1.00  
% 1.92/1.00  ------ BMC1 Options
% 1.92/1.00  
% 1.92/1.00  --bmc1_incremental                      false
% 1.92/1.00  --bmc1_axioms                           reachable_all
% 1.92/1.00  --bmc1_min_bound                        0
% 1.92/1.00  --bmc1_max_bound                        -1
% 1.92/1.00  --bmc1_max_bound_default                -1
% 1.92/1.00  --bmc1_symbol_reachability              true
% 1.92/1.00  --bmc1_property_lemmas                  false
% 1.92/1.00  --bmc1_k_induction                      false
% 1.92/1.00  --bmc1_non_equiv_states                 false
% 1.92/1.00  --bmc1_deadlock                         false
% 1.92/1.00  --bmc1_ucm                              false
% 1.92/1.00  --bmc1_add_unsat_core                   none
% 1.92/1.00  --bmc1_unsat_core_children              false
% 1.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/1.00  --bmc1_out_stat                         full
% 1.92/1.00  --bmc1_ground_init                      false
% 1.92/1.00  --bmc1_pre_inst_next_state              false
% 1.92/1.00  --bmc1_pre_inst_state                   false
% 1.92/1.00  --bmc1_pre_inst_reach_state             false
% 1.92/1.00  --bmc1_out_unsat_core                   false
% 1.92/1.00  --bmc1_aig_witness_out                  false
% 1.92/1.00  --bmc1_verbose                          false
% 1.92/1.00  --bmc1_dump_clauses_tptp                false
% 1.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.92/1.00  --bmc1_dump_file                        -
% 1.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.92/1.00  --bmc1_ucm_extend_mode                  1
% 1.92/1.00  --bmc1_ucm_init_mode                    2
% 1.92/1.00  --bmc1_ucm_cone_mode                    none
% 1.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.92/1.00  --bmc1_ucm_relax_model                  4
% 1.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/1.00  --bmc1_ucm_layered_model                none
% 1.92/1.00  --bmc1_ucm_max_lemma_size               10
% 1.92/1.00  
% 1.92/1.00  ------ AIG Options
% 1.92/1.00  
% 1.92/1.00  --aig_mode                              false
% 1.92/1.00  
% 1.92/1.00  ------ Instantiation Options
% 1.92/1.00  
% 1.92/1.00  --instantiation_flag                    true
% 1.92/1.00  --inst_sos_flag                         false
% 1.92/1.00  --inst_sos_phase                        true
% 1.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/1.00  --inst_lit_sel_side                     none
% 1.92/1.00  --inst_solver_per_active                1400
% 1.92/1.00  --inst_solver_calls_frac                1.
% 1.92/1.00  --inst_passive_queue_type               priority_queues
% 1.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/1.00  --inst_passive_queues_freq              [25;2]
% 1.92/1.00  --inst_dismatching                      true
% 1.92/1.00  --inst_eager_unprocessed_to_passive     true
% 1.92/1.00  --inst_prop_sim_given                   true
% 1.92/1.00  --inst_prop_sim_new                     false
% 1.92/1.00  --inst_subs_new                         false
% 1.92/1.00  --inst_eq_res_simp                      false
% 1.92/1.00  --inst_subs_given                       false
% 1.92/1.00  --inst_orphan_elimination               true
% 1.92/1.00  --inst_learning_loop_flag               true
% 1.92/1.00  --inst_learning_start                   3000
% 1.92/1.00  --inst_learning_factor                  2
% 1.92/1.00  --inst_start_prop_sim_after_learn       3
% 1.92/1.00  --inst_sel_renew                        solver
% 1.92/1.00  --inst_lit_activity_flag                true
% 1.92/1.00  --inst_restr_to_given                   false
% 1.92/1.00  --inst_activity_threshold               500
% 1.92/1.00  --inst_out_proof                        true
% 1.92/1.00  
% 1.92/1.00  ------ Resolution Options
% 1.92/1.00  
% 1.92/1.00  --resolution_flag                       false
% 1.92/1.00  --res_lit_sel                           adaptive
% 1.92/1.00  --res_lit_sel_side                      none
% 1.92/1.00  --res_ordering                          kbo
% 1.92/1.00  --res_to_prop_solver                    active
% 1.92/1.00  --res_prop_simpl_new                    false
% 1.92/1.00  --res_prop_simpl_given                  true
% 1.92/1.00  --res_passive_queue_type                priority_queues
% 1.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/1.00  --res_passive_queues_freq               [15;5]
% 1.92/1.00  --res_forward_subs                      full
% 1.92/1.00  --res_backward_subs                     full
% 1.92/1.00  --res_forward_subs_resolution           true
% 1.92/1.00  --res_backward_subs_resolution          true
% 1.92/1.00  --res_orphan_elimination                true
% 1.92/1.00  --res_time_limit                        2.
% 1.92/1.00  --res_out_proof                         true
% 1.92/1.00  
% 1.92/1.00  ------ Superposition Options
% 1.92/1.00  
% 1.92/1.00  --superposition_flag                    true
% 1.92/1.00  --sup_passive_queue_type                priority_queues
% 1.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.92/1.00  --demod_completeness_check              fast
% 1.92/1.00  --demod_use_ground                      true
% 1.92/1.00  --sup_to_prop_solver                    passive
% 1.92/1.00  --sup_prop_simpl_new                    true
% 1.92/1.00  --sup_prop_simpl_given                  true
% 1.92/1.00  --sup_fun_splitting                     false
% 1.92/1.00  --sup_smt_interval                      50000
% 1.92/1.00  
% 1.92/1.00  ------ Superposition Simplification Setup
% 1.92/1.00  
% 1.92/1.00  --sup_indices_passive                   []
% 1.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.00  --sup_full_bw                           [BwDemod]
% 1.92/1.00  --sup_immed_triv                        [TrivRules]
% 1.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.00  --sup_immed_bw_main                     []
% 1.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/1.00  
% 1.92/1.00  ------ Combination Options
% 1.92/1.00  
% 1.92/1.00  --comb_res_mult                         3
% 1.92/1.00  --comb_sup_mult                         2
% 1.92/1.00  --comb_inst_mult                        10
% 1.92/1.00  
% 1.92/1.00  ------ Debug Options
% 1.92/1.00  
% 1.92/1.00  --dbg_backtrace                         false
% 1.92/1.00  --dbg_dump_prop_clauses                 false
% 1.92/1.00  --dbg_dump_prop_clauses_file            -
% 1.92/1.00  --dbg_out_stat                          false
% 1.92/1.00  
% 1.92/1.00  
% 1.92/1.00  
% 1.92/1.00  
% 1.92/1.00  ------ Proving...
% 1.92/1.00  
% 1.92/1.00  
% 1.92/1.00  % SZS status Theorem for theBenchmark.p
% 1.92/1.00  
% 1.92/1.00   Resolution empty clause
% 1.92/1.00  
% 1.92/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.92/1.00  
% 1.92/1.00  fof(f6,axiom,(
% 1.92/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f61,plain,(
% 1.92/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.92/1.00    inference(cnf_transformation,[],[f6])).
% 1.92/1.00  
% 1.92/1.00  fof(f4,axiom,(
% 1.92/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f19,plain,(
% 1.92/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.92/1.00    inference(ennf_transformation,[],[f4])).
% 1.92/1.00  
% 1.92/1.00  fof(f59,plain,(
% 1.92/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.92/1.00    inference(cnf_transformation,[],[f19])).
% 1.92/1.00  
% 1.92/1.00  fof(f2,axiom,(
% 1.92/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f57,plain,(
% 1.92/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.92/1.00    inference(cnf_transformation,[],[f2])).
% 1.92/1.00  
% 1.92/1.00  fof(f15,axiom,(
% 1.92/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f33,plain,(
% 1.92/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(ennf_transformation,[],[f15])).
% 1.92/1.00  
% 1.92/1.00  fof(f49,plain,(
% 1.92/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(nnf_transformation,[],[f33])).
% 1.92/1.00  
% 1.92/1.00  fof(f82,plain,(
% 1.92/1.00    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f49])).
% 1.92/1.00  
% 1.92/1.00  fof(f16,conjecture,(
% 1.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f17,negated_conjecture,(
% 1.92/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.92/1.00    inference(negated_conjecture,[],[f16])).
% 1.92/1.00  
% 1.92/1.00  fof(f34,plain,(
% 1.92/1.00    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.92/1.00    inference(ennf_transformation,[],[f17])).
% 1.92/1.00  
% 1.92/1.00  fof(f35,plain,(
% 1.92/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.92/1.00    inference(flattening,[],[f34])).
% 1.92/1.00  
% 1.92/1.00  fof(f50,plain,(
% 1.92/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.92/1.00    inference(nnf_transformation,[],[f35])).
% 1.92/1.00  
% 1.92/1.00  fof(f51,plain,(
% 1.92/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.92/1.00    inference(flattening,[],[f50])).
% 1.92/1.00  
% 1.92/1.00  fof(f54,plain,(
% 1.92/1.00    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK6 & ! [X3] : (((r2_hidden(X3,sK6) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK6))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.92/1.00    introduced(choice_axiom,[])).
% 1.92/1.00  
% 1.92/1.00  fof(f53,plain,(
% 1.92/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK5,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK5,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.92/1.00    introduced(choice_axiom,[])).
% 1.92/1.00  
% 1.92/1.00  fof(f52,plain,(
% 1.92/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK4) | ~v3_pre_topc(X3,sK4)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK4) & v3_pre_topc(X3,sK4)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 1.92/1.00    introduced(choice_axiom,[])).
% 1.92/1.00  
% 1.92/1.00  fof(f55,plain,(
% 1.92/1.00    ((k1_xboole_0 = sK6 & ! [X3] : (((r2_hidden(X3,sK6) | ~r2_hidden(sK5,X3) | ~v4_pre_topc(X3,sK4) | ~v3_pre_topc(X3,sK4)) & ((r2_hidden(sK5,X3) & v4_pre_topc(X3,sK4) & v3_pre_topc(X3,sK4)) | ~r2_hidden(X3,sK6))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 1.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f54,f53,f52])).
% 1.92/1.00  
% 1.92/1.00  fof(f92,plain,(
% 1.92/1.00    ( ! [X3] : (r2_hidden(X3,sK6) | ~r2_hidden(sK5,X3) | ~v4_pre_topc(X3,sK4) | ~v3_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 1.92/1.00    inference(cnf_transformation,[],[f55])).
% 1.92/1.00  
% 1.92/1.00  fof(f86,plain,(
% 1.92/1.00    l1_pre_topc(sK4)),
% 1.92/1.00    inference(cnf_transformation,[],[f55])).
% 1.92/1.00  
% 1.92/1.00  fof(f93,plain,(
% 1.92/1.00    k1_xboole_0 = sK6),
% 1.92/1.00    inference(cnf_transformation,[],[f55])).
% 1.92/1.00  
% 1.92/1.00  fof(f1,axiom,(
% 1.92/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f56,plain,(
% 1.92/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f1])).
% 1.92/1.00  
% 1.92/1.00  fof(f9,axiom,(
% 1.92/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f24,plain,(
% 1.92/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.92/1.00    inference(ennf_transformation,[],[f9])).
% 1.92/1.00  
% 1.92/1.00  fof(f64,plain,(
% 1.92/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f24])).
% 1.92/1.00  
% 1.92/1.00  fof(f85,plain,(
% 1.92/1.00    v2_pre_topc(sK4)),
% 1.92/1.00    inference(cnf_transformation,[],[f55])).
% 1.92/1.00  
% 1.92/1.00  fof(f87,plain,(
% 1.92/1.00    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.92/1.00    inference(cnf_transformation,[],[f55])).
% 1.92/1.00  
% 1.92/1.00  fof(f14,axiom,(
% 1.92/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => r2_hidden(k1_xboole_0,u1_pre_topc(X0)))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f31,plain,(
% 1.92/1.00    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.92/1.00    inference(ennf_transformation,[],[f14])).
% 1.92/1.00  
% 1.92/1.00  fof(f32,plain,(
% 1.92/1.00    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.92/1.00    inference(flattening,[],[f31])).
% 1.92/1.00  
% 1.92/1.00  fof(f81,plain,(
% 1.92/1.00    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f32])).
% 1.92/1.00  
% 1.92/1.00  fof(f10,axiom,(
% 1.92/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f18,plain,(
% 1.92/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.92/1.00    inference(rectify,[],[f10])).
% 1.92/1.00  
% 1.92/1.00  fof(f25,plain,(
% 1.92/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(ennf_transformation,[],[f18])).
% 1.92/1.00  
% 1.92/1.00  fof(f26,plain,(
% 1.92/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(flattening,[],[f25])).
% 1.92/1.00  
% 1.92/1.00  fof(f36,plain,(
% 1.92/1.00    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.92/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.92/1.00  
% 1.92/1.00  fof(f37,plain,(
% 1.92/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(definition_folding,[],[f26,f36])).
% 1.92/1.00  
% 1.92/1.00  fof(f43,plain,(
% 1.92/1.00    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(nnf_transformation,[],[f37])).
% 1.92/1.00  
% 1.92/1.00  fof(f44,plain,(
% 1.92/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(flattening,[],[f43])).
% 1.92/1.00  
% 1.92/1.00  fof(f45,plain,(
% 1.92/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(rectify,[],[f44])).
% 1.92/1.00  
% 1.92/1.00  fof(f46,plain,(
% 1.92/1.00    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.92/1.00    introduced(choice_axiom,[])).
% 1.92/1.00  
% 1.92/1.00  fof(f47,plain,(
% 1.92/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 1.92/1.00  
% 1.92/1.00  fof(f71,plain,(
% 1.92/1.00    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f47])).
% 1.92/1.00  
% 1.92/1.00  fof(f11,axiom,(
% 1.92/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f27,plain,(
% 1.92/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(ennf_transformation,[],[f11])).
% 1.92/1.00  
% 1.92/1.00  fof(f48,plain,(
% 1.92/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(nnf_transformation,[],[f27])).
% 1.92/1.00  
% 1.92/1.00  fof(f78,plain,(
% 1.92/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f48])).
% 1.92/1.00  
% 1.92/1.00  fof(f7,axiom,(
% 1.92/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f20,plain,(
% 1.92/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.92/1.00    inference(ennf_transformation,[],[f7])).
% 1.92/1.00  
% 1.92/1.00  fof(f21,plain,(
% 1.92/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.92/1.00    inference(flattening,[],[f20])).
% 1.92/1.00  
% 1.92/1.00  fof(f62,plain,(
% 1.92/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f21])).
% 1.92/1.00  
% 1.92/1.00  fof(f13,axiom,(
% 1.92/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f29,plain,(
% 1.92/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.92/1.00    inference(ennf_transformation,[],[f13])).
% 1.92/1.00  
% 1.92/1.00  fof(f30,plain,(
% 1.92/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.92/1.00    inference(flattening,[],[f29])).
% 1.92/1.00  
% 1.92/1.00  fof(f80,plain,(
% 1.92/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f30])).
% 1.92/1.00  
% 1.92/1.00  fof(f84,plain,(
% 1.92/1.00    ~v2_struct_0(sK4)),
% 1.92/1.00    inference(cnf_transformation,[],[f55])).
% 1.92/1.00  
% 1.92/1.00  fof(f12,axiom,(
% 1.92/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f28,plain,(
% 1.92/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.92/1.00    inference(ennf_transformation,[],[f12])).
% 1.92/1.00  
% 1.92/1.00  fof(f79,plain,(
% 1.92/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.92/1.00    inference(cnf_transformation,[],[f28])).
% 1.92/1.00  
% 1.92/1.00  fof(f5,axiom,(
% 1.92/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f60,plain,(
% 1.92/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.92/1.00    inference(cnf_transformation,[],[f5])).
% 1.92/1.00  
% 1.92/1.00  fof(f3,axiom,(
% 1.92/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 1.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/1.00  
% 1.92/1.00  fof(f58,plain,(
% 1.92/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.92/1.00    inference(cnf_transformation,[],[f3])).
% 1.92/1.00  
% 1.92/1.00  cnf(c_5,plain,
% 1.92/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.92/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1678,plain,
% 1.92/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_3,plain,
% 1.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.92/1.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 1.92/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1680,plain,
% 1.92/1.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 1.92/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_2468,plain,
% 1.92/1.00      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 1.92/1.00      inference(superposition,[status(thm)],[c_1678,c_1680]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1,plain,
% 1.92/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.92/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_2473,plain,
% 1.92/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 1.92/1.00      inference(light_normalisation,[status(thm)],[c_2468,c_1]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_27,plain,
% 1.92/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 1.92/1.00      | ~ v3_pre_topc(X1,X0)
% 1.92/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.92/1.00      | ~ l1_pre_topc(X0) ),
% 1.92/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_29,negated_conjecture,
% 1.92/1.00      ( ~ v4_pre_topc(X0,sK4)
% 1.92/1.00      | ~ v3_pre_topc(X0,sK4)
% 1.92/1.00      | r2_hidden(X0,sK6)
% 1.92/1.00      | ~ r2_hidden(sK5,X0)
% 1.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.92/1.00      inference(cnf_transformation,[],[f92]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_527,plain,
% 1.92/1.00      ( ~ v3_pre_topc(X0,X1)
% 1.92/1.00      | ~ v3_pre_topc(X2,sK4)
% 1.92/1.00      | r2_hidden(X2,sK6)
% 1.92/1.00      | ~ r2_hidden(sK5,X2)
% 1.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.92/1.00      | ~ l1_pre_topc(X1)
% 1.92/1.00      | k3_subset_1(u1_struct_0(X1),X0) != X2
% 1.92/1.00      | sK4 != X1 ),
% 1.92/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_29]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_528,plain,
% 1.92/1.00      ( ~ v3_pre_topc(X0,sK4)
% 1.92/1.00      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4)
% 1.92/1.00      | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),sK6)
% 1.92/1.00      | ~ r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0))
% 1.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.92/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.92/1.00      | ~ l1_pre_topc(sK4) ),
% 1.92/1.00      inference(unflattening,[status(thm)],[c_527]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_35,negated_conjecture,
% 1.92/1.00      ( l1_pre_topc(sK4) ),
% 1.92/1.00      inference(cnf_transformation,[],[f86]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_532,plain,
% 1.92/1.00      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.92/1.00      | ~ r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0))
% 1.92/1.00      | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),sK6)
% 1.92/1.00      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4)
% 1.92/1.00      | ~ v3_pre_topc(X0,sK4) ),
% 1.92/1.00      inference(global_propositional_subsumption,[status(thm)],[c_528,c_35]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_533,plain,
% 1.92/1.00      ( ~ v3_pre_topc(X0,sK4)
% 1.92/1.00      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4)
% 1.92/1.00      | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),sK6)
% 1.92/1.00      | ~ r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0))
% 1.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.92/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.92/1.00      inference(renaming,[status(thm)],[c_532]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1664,plain,
% 1.92/1.00      ( v3_pre_topc(X0,sK4) != iProver_top
% 1.92/1.00      | v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4) != iProver_top
% 1.92/1.00      | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),sK6) = iProver_top
% 1.92/1.00      | r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0)) != iProver_top
% 1.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_28,negated_conjecture,
% 1.92/1.00      ( k1_xboole_0 = sK6 ),
% 1.92/1.00      inference(cnf_transformation,[],[f93]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1766,plain,
% 1.92/1.00      ( v3_pre_topc(X0,sK4) != iProver_top
% 1.92/1.00      | v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4) != iProver_top
% 1.92/1.00      | r2_hidden(k3_subset_1(u1_struct_0(sK4),X0),k1_xboole_0) = iProver_top
% 1.92/1.00      | r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0)) != iProver_top
% 1.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.92/1.00      inference(light_normalisation,[status(thm)],[c_1664,c_28]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_0,plain,
% 1.92/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 1.92/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_8,plain,
% 1.92/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.92/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_701,plain,
% 1.92/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.92/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_702,plain,
% 1.92/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.92/1.00      inference(unflattening,[status(thm)],[c_701]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1665,plain,
% 1.92/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1773,plain,
% 1.92/1.00      ( v3_pre_topc(X0,sK4) != iProver_top
% 1.92/1.00      | v3_pre_topc(k3_subset_1(u1_struct_0(sK4),X0),sK4) != iProver_top
% 1.92/1.00      | r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),X0)) != iProver_top
% 1.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK4),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.92/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1766,c_1665]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_2478,plain,
% 1.92/1.00      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK4),k1_xboole_0),sK4) != iProver_top
% 1.92/1.00      | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
% 1.92/1.00      | r2_hidden(sK5,k3_subset_1(u1_struct_0(sK4),k1_xboole_0)) != iProver_top
% 1.92/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.92/1.00      inference(superposition,[status(thm)],[c_2473,c_1773]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_2479,plain,
% 1.92/1.00      ( v3_pre_topc(u1_struct_0(sK4),sK4) != iProver_top
% 1.92/1.00      | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
% 1.92/1.00      | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top
% 1.92/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.92/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.92/1.00      inference(demodulation,[status(thm)],[c_2478,c_2473]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_36,negated_conjecture,
% 1.92/1.00      ( v2_pre_topc(sK4) ),
% 1.92/1.00      inference(cnf_transformation,[],[f85]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_39,plain,
% 1.92/1.00      ( v2_pre_topc(sK4) = iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_40,plain,
% 1.92/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_34,negated_conjecture,
% 1.92/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.92/1.00      inference(cnf_transformation,[],[f87]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_41,plain,
% 1.92/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_25,plain,
% 1.92/1.00      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
% 1.92/1.00      | ~ l1_pre_topc(X0)
% 1.92/1.00      | ~ v2_pre_topc(X0) ),
% 1.92/1.00      inference(cnf_transformation,[],[f81]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_61,plain,
% 1.92/1.00      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0)) = iProver_top
% 1.92/1.00      | l1_pre_topc(X0) != iProver_top
% 1.92/1.00      | v2_pre_topc(X0) != iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_63,plain,
% 1.92/1.00      ( r2_hidden(k1_xboole_0,u1_pre_topc(sK4)) = iProver_top
% 1.92/1.00      | l1_pre_topc(sK4) != iProver_top
% 1.92/1.00      | v2_pre_topc(sK4) != iProver_top ),
% 1.92/1.00      inference(instantiation,[status(thm)],[c_61]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_20,plain,
% 1.92/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 1.92/1.00      | ~ l1_pre_topc(X0)
% 1.92/1.00      | ~ v2_pre_topc(X0) ),
% 1.92/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_76,plain,
% 1.92/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 1.92/1.00      | l1_pre_topc(X0) != iProver_top
% 1.92/1.00      | v2_pre_topc(X0) != iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_78,plain,
% 1.92/1.00      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top
% 1.92/1.00      | l1_pre_topc(sK4) != iProver_top
% 1.92/1.00      | v2_pre_topc(sK4) != iProver_top ),
% 1.92/1.00      inference(instantiation,[status(thm)],[c_76]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_21,plain,
% 1.92/1.00      ( v3_pre_topc(X0,X1)
% 1.92/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.00      | ~ l1_pre_topc(X1) ),
% 1.92/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_668,plain,
% 1.92/1.00      ( v3_pre_topc(X0,X1)
% 1.92/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/1.00      | sK4 != X1 ),
% 1.92/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_669,plain,
% 1.92/1.00      ( v3_pre_topc(X0,sK4)
% 1.92/1.00      | ~ r2_hidden(X0,u1_pre_topc(sK4))
% 1.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.92/1.00      inference(unflattening,[status(thm)],[c_668]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1831,plain,
% 1.92/1.00      ( v3_pre_topc(k1_xboole_0,sK4)
% 1.92/1.00      | ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK4))
% 1.92/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.92/1.00      inference(instantiation,[status(thm)],[c_669]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1832,plain,
% 1.92/1.00      ( v3_pre_topc(k1_xboole_0,sK4) = iProver_top
% 1.92/1.00      | r2_hidden(k1_xboole_0,u1_pre_topc(sK4)) != iProver_top
% 1.92/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1831]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_6,plain,
% 1.92/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.92/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_24,plain,
% 1.92/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.92/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_37,negated_conjecture,
% 1.92/1.00      ( ~ v2_struct_0(sK4) ),
% 1.92/1.00      inference(cnf_transformation,[],[f84]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_400,plain,
% 1.92/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK4 != X0 ),
% 1.92/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_37]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_401,plain,
% 1.92/1.00      ( ~ l1_struct_0(sK4) | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.92/1.00      inference(unflattening,[status(thm)],[c_400]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_65,plain,
% 1.92/1.00      ( v2_struct_0(sK4)
% 1.92/1.00      | ~ l1_struct_0(sK4)
% 1.92/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.92/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_23,plain,
% 1.92/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.92/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_68,plain,
% 1.92/1.00      ( l1_struct_0(sK4) | ~ l1_pre_topc(sK4) ),
% 1.92/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_403,plain,
% 1.92/1.00      ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.92/1.00      inference(global_propositional_subsumption,
% 1.92/1.00                [status(thm)],
% 1.92/1.00                [c_401,c_37,c_35,c_65,c_68]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_413,plain,
% 1.92/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | u1_struct_0(sK4) != X1 ),
% 1.92/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_403]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_414,plain,
% 1.92/1.00      ( r2_hidden(X0,u1_struct_0(sK4)) | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.92/1.00      inference(unflattening,[status(thm)],[c_413]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1843,plain,
% 1.92/1.00      ( r2_hidden(sK5,u1_struct_0(sK4)) | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.92/1.00      inference(instantiation,[status(thm)],[c_414]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1844,plain,
% 1.92/1.00      ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
% 1.92/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1843]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1846,plain,
% 1.92/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.92/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1848,plain,
% 1.92/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_1846]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_4,plain,
% 1.92/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.92/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1679,plain,
% 1.92/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_2,plain,
% 1.92/1.00      ( k2_subset_1(X0) = X0 ),
% 1.92/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1699,plain,
% 1.92/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.92/1.00      inference(light_normalisation,[status(thm)],[c_1679,c_2]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_1658,plain,
% 1.92/1.00      ( v3_pre_topc(X0,sK4) = iProver_top
% 1.92/1.00      | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
% 1.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.92/1.00      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_2168,plain,
% 1.92/1.00      ( v3_pre_topc(u1_struct_0(sK4),sK4) = iProver_top
% 1.92/1.00      | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top ),
% 1.92/1.00      inference(superposition,[status(thm)],[c_1699,c_1658]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_2629,plain,
% 1.92/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.92/1.00      inference(global_propositional_subsumption,
% 1.92/1.00                [status(thm)],
% 1.92/1.00                [c_2479,c_39,c_40,c_41,c_63,c_78,c_1832,c_1844,c_1848,c_2168]) ).
% 1.92/1.00  
% 1.92/1.00  cnf(c_2634,plain,
% 1.92/1.00      ( $false ),
% 1.92/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2629,c_1699]) ).
% 1.92/1.00  
% 1.92/1.00  
% 1.92/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.92/1.00  
% 1.92/1.00  ------                               Statistics
% 1.92/1.00  
% 1.92/1.00  ------ General
% 1.92/1.00  
% 1.92/1.00  abstr_ref_over_cycles:                  0
% 1.92/1.00  abstr_ref_under_cycles:                 0
% 1.92/1.00  gc_basic_clause_elim:                   0
% 1.92/1.00  forced_gc_time:                         0
% 1.92/1.00  parsing_time:                           0.01
% 1.92/1.00  unif_index_cands_time:                  0.
% 1.92/1.00  unif_index_add_time:                    0.
% 1.92/1.00  orderings_time:                         0.
% 1.92/1.00  out_proof_time:                         0.018
% 1.92/1.00  total_time:                             0.111
% 1.92/1.00  num_of_symbols:                         57
% 1.92/1.00  num_of_terms:                           1756
% 1.92/1.00  
% 1.92/1.00  ------ Preprocessing
% 1.92/1.00  
% 1.92/1.00  num_of_splits:                          0
% 1.92/1.00  num_of_split_atoms:                     0
% 1.92/1.00  num_of_reused_defs:                     0
% 1.92/1.00  num_eq_ax_congr_red:                    20
% 1.92/1.00  num_of_sem_filtered_clauses:            1
% 1.92/1.00  num_of_subtypes:                        0
% 1.92/1.00  monotx_restored_types:                  0
% 1.92/1.00  sat_num_of_epr_types:                   0
% 1.92/1.00  sat_num_of_non_cyclic_types:            0
% 1.92/1.00  sat_guarded_non_collapsed_types:        0
% 1.92/1.00  num_pure_diseq_elim:                    0
% 1.92/1.00  simp_replaced_by:                       0
% 1.92/1.00  res_preprocessed:                       146
% 1.92/1.00  prep_upred:                             0
% 1.92/1.00  prep_unflattend:                        38
% 1.92/1.00  smt_new_axioms:                         0
% 1.92/1.00  pred_elim_cands:                        4
% 1.92/1.00  pred_elim:                              7
% 1.92/1.00  pred_elim_cl:                           11
% 1.92/1.00  pred_elim_cycles:                       10
% 1.92/1.00  merged_defs:                            0
% 1.92/1.00  merged_defs_ncl:                        0
% 1.92/1.00  bin_hyper_res:                          0
% 1.92/1.00  prep_cycles:                            4
% 1.92/1.00  pred_elim_time:                         0.013
% 1.92/1.00  splitting_time:                         0.
% 1.92/1.00  sem_filter_time:                        0.
% 1.92/1.00  monotx_time:                            0.
% 1.92/1.00  subtype_inf_time:                       0.
% 1.92/1.00  
% 1.92/1.00  ------ Problem properties
% 1.92/1.00  
% 1.92/1.00  clauses:                                27
% 1.92/1.00  conjectures:                            5
% 1.92/1.00  epr:                                    3
% 1.92/1.00  horn:                                   23
% 1.92/1.00  ground:                                 7
% 1.92/1.00  unary:                                  12
% 1.92/1.00  binary:                                 7
% 1.92/1.00  lits:                                   57
% 1.92/1.00  lits_eq:                                4
% 1.92/1.00  fd_pure:                                0
% 1.92/1.00  fd_pseudo:                              0
% 1.92/1.00  fd_cond:                                0
% 1.92/1.00  fd_pseudo_cond:                         0
% 1.92/1.00  ac_symbols:                             0
% 1.92/1.00  
% 1.92/1.00  ------ Propositional Solver
% 1.92/1.00  
% 1.92/1.00  prop_solver_calls:                      25
% 1.92/1.00  prop_fast_solver_calls:                 872
% 1.92/1.00  smt_solver_calls:                       0
% 1.92/1.00  smt_fast_solver_calls:                  0
% 1.92/1.00  prop_num_of_clauses:                    675
% 1.92/1.00  prop_preprocess_simplified:             4416
% 1.92/1.00  prop_fo_subsumed:                       14
% 1.92/1.00  prop_solver_time:                       0.
% 1.92/1.00  smt_solver_time:                        0.
% 1.92/1.00  smt_fast_solver_time:                   0.
% 1.92/1.00  prop_fast_solver_time:                  0.
% 1.92/1.00  prop_unsat_core_time:                   0.
% 1.92/1.00  
% 1.92/1.00  ------ QBF
% 1.92/1.00  
% 1.92/1.00  qbf_q_res:                              0
% 1.92/1.00  qbf_num_tautologies:                    0
% 1.92/1.00  qbf_prep_cycles:                        0
% 1.92/1.00  
% 1.92/1.00  ------ BMC1
% 1.92/1.00  
% 1.92/1.00  bmc1_current_bound:                     -1
% 1.92/1.00  bmc1_last_solved_bound:                 -1
% 1.92/1.00  bmc1_unsat_core_size:                   -1
% 1.92/1.00  bmc1_unsat_core_parents_size:           -1
% 1.92/1.00  bmc1_merge_next_fun:                    0
% 1.92/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.92/1.00  
% 1.92/1.00  ------ Instantiation
% 1.92/1.00  
% 1.92/1.00  inst_num_of_clauses:                    184
% 1.92/1.00  inst_num_in_passive:                    68
% 1.92/1.00  inst_num_in_active:                     108
% 1.92/1.00  inst_num_in_unprocessed:                8
% 1.92/1.00  inst_num_of_loops:                      110
% 1.92/1.00  inst_num_of_learning_restarts:          0
% 1.92/1.00  inst_num_moves_active_passive:          0
% 1.92/1.00  inst_lit_activity:                      0
% 1.92/1.00  inst_lit_activity_moves:                0
% 1.92/1.00  inst_num_tautologies:                   0
% 1.92/1.00  inst_num_prop_implied:                  0
% 1.92/1.00  inst_num_existing_simplified:           0
% 1.92/1.00  inst_num_eq_res_simplified:             0
% 1.92/1.00  inst_num_child_elim:                    0
% 1.92/1.00  inst_num_of_dismatching_blockings:      25
% 1.92/1.00  inst_num_of_non_proper_insts:           106
% 1.92/1.00  inst_num_of_duplicates:                 0
% 1.92/1.00  inst_inst_num_from_inst_to_res:         0
% 1.92/1.00  inst_dismatching_checking_time:         0.
% 1.92/1.00  
% 1.92/1.00  ------ Resolution
% 1.92/1.00  
% 1.92/1.00  res_num_of_clauses:                     0
% 1.92/1.00  res_num_in_passive:                     0
% 1.92/1.00  res_num_in_active:                      0
% 1.92/1.00  res_num_of_loops:                       150
% 1.92/1.00  res_forward_subset_subsumed:            15
% 1.92/1.00  res_backward_subset_subsumed:           0
% 1.92/1.00  res_forward_subsumed:                   0
% 1.92/1.00  res_backward_subsumed:                  0
% 1.92/1.00  res_forward_subsumption_resolution:     1
% 1.92/1.00  res_backward_subsumption_resolution:    0
% 1.92/1.00  res_clause_to_clause_subsumption:       114
% 1.92/1.00  res_orphan_elimination:                 0
% 1.92/1.00  res_tautology_del:                      8
% 1.92/1.00  res_num_eq_res_simplified:              0
% 1.92/1.00  res_num_sel_changes:                    0
% 1.92/1.00  res_moves_from_active_to_pass:          0
% 1.92/1.00  
% 1.92/1.00  ------ Superposition
% 1.92/1.00  
% 1.92/1.00  sup_time_total:                         0.
% 1.92/1.00  sup_time_generating:                    0.
% 1.92/1.00  sup_time_sim_full:                      0.
% 1.92/1.00  sup_time_sim_immed:                     0.
% 1.92/1.00  
% 1.92/1.00  sup_num_of_clauses:                     28
% 1.92/1.00  sup_num_in_active:                      20
% 1.92/1.00  sup_num_in_passive:                     8
% 1.92/1.00  sup_num_of_loops:                       20
% 1.92/1.00  sup_fw_superposition:                   3
% 1.92/1.00  sup_bw_superposition:                   5
% 1.92/1.00  sup_immediate_simplified:               4
% 1.92/1.00  sup_given_eliminated:                   0
% 1.92/1.00  comparisons_done:                       0
% 1.92/1.00  comparisons_avoided:                    0
% 1.92/1.00  
% 1.92/1.00  ------ Simplifications
% 1.92/1.00  
% 1.92/1.00  
% 1.92/1.00  sim_fw_subset_subsumed:                 2
% 1.92/1.00  sim_bw_subset_subsumed:                 0
% 1.92/1.00  sim_fw_subsumed:                        4
% 1.92/1.00  sim_bw_subsumed:                        0
% 1.92/1.00  sim_fw_subsumption_res:                 2
% 1.92/1.00  sim_bw_subsumption_res:                 0
% 1.92/1.00  sim_tautology_del:                      0
% 1.92/1.00  sim_eq_tautology_del:                   0
% 1.92/1.00  sim_eq_res_simp:                        0
% 1.92/1.00  sim_fw_demodulated:                     1
% 1.92/1.00  sim_bw_demodulated:                     0
% 1.92/1.00  sim_light_normalised:                   7
% 1.92/1.00  sim_joinable_taut:                      0
% 1.92/1.00  sim_joinable_simp:                      0
% 1.92/1.00  sim_ac_normalised:                      0
% 1.92/1.00  sim_smt_subsumption:                    0
% 1.92/1.00  
%------------------------------------------------------------------------------
