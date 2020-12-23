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
% DateTime   : Thu Dec  3 12:18:42 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 505 expanded)
%              Number of clauses        :   67 ( 104 expanded)
%              Number of leaves         :   23 ( 142 expanded)
%              Depth                    :   21
%              Number of atoms          :  546 (4834 expanded)
%              Number of equality atoms :   96 ( 478 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f48,plain,(
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
     => ( k1_xboole_0 = sK4
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK4)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK4) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
                    | ~ r2_hidden(sK3,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK3,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
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
                      | ~ v4_pre_topc(X3,sK2)
                      | ~ v3_pre_topc(X3,sK2) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK2)
                        & v3_pre_topc(X3,sK2) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k1_xboole_0 = sK4
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK4)
            | ~ r2_hidden(sK3,X3)
            | ~ v4_pre_topc(X3,sK2)
            | ~ v3_pre_topc(X3,sK2) )
          & ( ( r2_hidden(sK3,X3)
              & v4_pre_topc(X3,sK2)
              & v3_pre_topc(X3,sK2) )
            | ~ r2_hidden(X3,sK4) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).

fof(f83,plain,(
    k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    ! [X0] : r1_tarski(sK4,X0) ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f84])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f85,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,sK4)) = sK4 ),
    inference(definition_unfolding,[],[f51,f58,f83,f83])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(X0,sK4) = X0 ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X4),X1)
        & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK1(X0,X1,X4),X1)
                    & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1,negated_conjecture,
    ( r1_tarski(sK4,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_517,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_518,plain,
    ( ~ r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_2189,plain,
    ( ~ r2_hidden(sK0(sK2,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1318,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1320,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1762,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK4))) = k3_subset_1(X0,sK4) ),
    inference(superposition,[status(thm)],[c_1318,c_1320])).

cnf(c_0,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X0,sK4)) = sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2,negated_conjecture,
    ( k5_xboole_0(X0,sK4) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1767,plain,
    ( k3_subset_1(X0,sK4) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1762,c_0,c_2])).

cnf(c_15,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X0,sK2)
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_451,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,sK2)
    | r2_hidden(X2,sK4)
    | ~ r2_hidden(sK3,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),X0) != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_452,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
    | r2_hidden(k3_subset_1(u1_struct_0(sK2),X0),sK4)
    | ~ r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_456,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0))
    | r2_hidden(k3_subset_1(u1_struct_0(sK2),X0),sK4)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_28])).

cnf(c_457,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
    | r2_hidden(k3_subset_1(u1_struct_0(sK2),X0),sK4)
    | ~ r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_643,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
    | ~ r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_518,c_457])).

cnf(c_1313,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2) != iProver_top
    | r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_363,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_10])).

cnf(c_855,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_363,c_28])).

cnf(c_856,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_1389,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK2),X0),sK2) != iProver_top
    | r2_hidden(sK3,k3_subset_1(k2_struct_0(sK2),X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK2),X0),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1313,c_856])).

cnf(c_2026,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK2),sK4),sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | r2_hidden(sK3,k3_subset_1(k2_struct_0(sK2),sK4)) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_1389])).

cnf(c_2027,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2026,c_1767])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_33,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_80,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_82,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1315,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1331,plain,
    ( m1_subset_1(sK3,k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1315,c_856])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_349,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_11,c_12])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_663,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_349,c_30])).

cnf(c_664,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_84,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_87,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_666,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_664,c_30,c_28,c_84,c_87])).

cnf(c_827,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_666])).

cnf(c_828,plain,
    ( r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_1309,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_1342,plain,
    ( r2_hidden(X0,k2_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1309,c_856])).

cnf(c_1621,plain,
    ( r2_hidden(sK3,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1331,c_1342])).

cnf(c_2129,plain,
    ( v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2027,c_32,c_33,c_82,c_1621])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1319,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1338,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1319,c_3])).

cnf(c_2136,plain,
    ( v3_pre_topc(sK4,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2129,c_1318,c_1338])).

cnf(c_2137,plain,
    ( ~ v3_pre_topc(sK4,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2136])).

cnf(c_17,plain,
    ( v3_pre_topc(X0,X1)
    | r2_hidden(sK0(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_779,plain,
    ( v3_pre_topc(X0,X1)
    | r2_hidden(sK0(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_780,plain,
    ( v3_pre_topc(X0,sK2)
    | r2_hidden(sK0(sK2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_784,plain,
    ( v3_pre_topc(X0,sK2)
    | r2_hidden(sK0(sK2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_29,c_28])).

cnf(c_1543,plain,
    ( v3_pre_topc(sK4,sK2)
    | r2_hidden(sK0(sK2,sK4),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1460,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2189,c_2137,c_1543,c_1460])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.09/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/0.99  
% 2.09/0.99  ------  iProver source info
% 2.09/0.99  
% 2.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/0.99  git: non_committed_changes: false
% 2.09/0.99  git: last_make_outside_of_git: false
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     num_symb
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       true
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  ------ Parsing...
% 2.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/0.99  ------ Proving...
% 2.09/0.99  ------ Problem Properties 
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  clauses                                 19
% 2.09/0.99  conjectures                             5
% 2.09/0.99  EPR                                     1
% 2.09/0.99  Horn                                    17
% 2.09/0.99  unary                                   10
% 2.09/0.99  binary                                  2
% 2.09/0.99  lits                                    42
% 2.09/0.99  lits eq                                 6
% 2.09/0.99  fd_pure                                 0
% 2.09/0.99  fd_pseudo                               0
% 2.09/0.99  fd_cond                                 0
% 2.09/0.99  fd_pseudo_cond                          0
% 2.09/0.99  AC symbols                              0
% 2.09/0.99  
% 2.09/0.99  ------ Schedule dynamic 5 is on 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  Current options:
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     none
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       false
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ Proving...
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS status Theorem for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  fof(f3,axiom,(
% 2.09/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f52,plain,(
% 2.09/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f3])).
% 2.09/0.99  
% 2.09/0.99  fof(f19,conjecture,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f20,negated_conjecture,(
% 2.09/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 2.09/0.99    inference(negated_conjecture,[],[f19])).
% 2.09/0.99  
% 2.09/0.99  fof(f36,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f20])).
% 2.09/0.99  
% 2.09/0.99  fof(f37,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f36])).
% 2.09/0.99  
% 2.09/0.99  fof(f44,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f37])).
% 2.09/0.99  
% 2.09/0.99  fof(f45,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f44])).
% 2.09/0.99  
% 2.09/0.99  fof(f48,plain,(
% 2.09/0.99    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f47,plain,(
% 2.09/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f46,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f49,plain,(
% 2.09/0.99    ((k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).
% 2.09/0.99  
% 2.09/0.99  fof(f83,plain,(
% 2.09/0.99    k1_xboole_0 = sK4),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f86,plain,(
% 2.09/0.99    ( ! [X0] : (r1_tarski(sK4,X0)) )),
% 2.09/0.99    inference(definition_unfolding,[],[f52,f83])).
% 2.09/0.99  
% 2.09/0.99  fof(f12,axiom,(
% 2.09/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f26,plain,(
% 2.09/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.09/0.99    inference(ennf_transformation,[],[f12])).
% 2.09/0.99  
% 2.09/0.99  fof(f61,plain,(
% 2.09/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f26])).
% 2.09/0.99  
% 2.09/0.99  fof(f8,axiom,(
% 2.09/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f57,plain,(
% 2.09/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f8])).
% 2.09/0.99  
% 2.09/0.99  fof(f89,plain,(
% 2.09/0.99    ( ! [X0] : (m1_subset_1(sK4,k1_zfmisc_1(X0))) )),
% 2.09/0.99    inference(definition_unfolding,[],[f57,f83])).
% 2.09/0.99  
% 2.09/0.99  fof(f6,axiom,(
% 2.09/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f21,plain,(
% 2.09/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f6])).
% 2.09/0.99  
% 2.09/0.99  fof(f55,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f21])).
% 2.09/0.99  
% 2.09/0.99  fof(f1,axiom,(
% 2.09/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f50,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f1])).
% 2.09/0.99  
% 2.09/0.99  fof(f9,axiom,(
% 2.09/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f58,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f9])).
% 2.09/0.99  
% 2.09/0.99  fof(f84,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.09/0.99    inference(definition_unfolding,[],[f50,f58])).
% 2.09/0.99  
% 2.09/0.99  fof(f88,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.99    inference(definition_unfolding,[],[f55,f84])).
% 2.09/0.99  
% 2.09/0.99  fof(f2,axiom,(
% 2.09/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f51,plain,(
% 2.09/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.09/0.99    inference(cnf_transformation,[],[f2])).
% 2.09/0.99  
% 2.09/0.99  fof(f85,plain,(
% 2.09/0.99    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,sK4)) = sK4) )),
% 2.09/0.99    inference(definition_unfolding,[],[f51,f58,f83,f83])).
% 2.09/0.99  
% 2.09/0.99  fof(f4,axiom,(
% 2.09/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f53,plain,(
% 2.09/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.09/0.99    inference(cnf_transformation,[],[f4])).
% 2.09/0.99  
% 2.09/0.99  fof(f87,plain,(
% 2.09/0.99    ( ! [X0] : (k5_xboole_0(X0,sK4) = X0) )),
% 2.09/0.99    inference(definition_unfolding,[],[f53,f83])).
% 2.09/0.99  
% 2.09/0.99  fof(f17,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f33,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f17])).
% 2.09/0.99  
% 2.09/0.99  fof(f38,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f33])).
% 2.09/0.99  
% 2.09/0.99  fof(f66,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f82,plain,(
% 2.09/0.99    ( ! [X3] : (r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f76,plain,(
% 2.09/0.99    l1_pre_topc(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f14,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f28,plain,(
% 2.09/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f14])).
% 2.09/0.99  
% 2.09/0.99  fof(f63,plain,(
% 2.09/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f28])).
% 2.09/0.99  
% 2.09/0.99  fof(f13,axiom,(
% 2.09/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f27,plain,(
% 2.09/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f13])).
% 2.09/0.99  
% 2.09/0.99  fof(f62,plain,(
% 2.09/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f75,plain,(
% 2.09/0.99    v2_pre_topc(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f16,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f31,plain,(
% 2.09/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f16])).
% 2.09/0.99  
% 2.09/0.99  fof(f32,plain,(
% 2.09/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.99    inference(flattening,[],[f31])).
% 2.09/0.99  
% 2.09/0.99  fof(f65,plain,(
% 2.09/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f32])).
% 2.09/0.99  
% 2.09/0.99  fof(f77,plain,(
% 2.09/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f10,axiom,(
% 2.09/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f22,plain,(
% 2.09/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.09/0.99    inference(ennf_transformation,[],[f10])).
% 2.09/0.99  
% 2.09/0.99  fof(f23,plain,(
% 2.09/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.09/0.99    inference(flattening,[],[f22])).
% 2.09/0.99  
% 2.09/0.99  fof(f59,plain,(
% 2.09/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f23])).
% 2.09/0.99  
% 2.09/0.99  fof(f15,axiom,(
% 2.09/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f29,plain,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f30,plain,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f29])).
% 2.09/0.99  
% 2.09/0.99  fof(f64,plain,(
% 2.09/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f30])).
% 2.09/0.99  
% 2.09/0.99  fof(f74,plain,(
% 2.09/0.99    ~v2_struct_0(sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f7,axiom,(
% 2.09/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f56,plain,(
% 2.09/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f7])).
% 2.09/0.99  
% 2.09/0.99  fof(f5,axiom,(
% 2.09/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f54,plain,(
% 2.09/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.09/0.99    inference(cnf_transformation,[],[f5])).
% 2.09/0.99  
% 2.09/0.99  fof(f18,axiom,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f34,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f18])).
% 2.09/0.99  
% 2.09/0.99  fof(f35,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f34])).
% 2.09/0.99  
% 2.09/0.99  fof(f39,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f35])).
% 2.09/0.99  
% 2.09/0.99  fof(f40,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(rectify,[],[f39])).
% 2.09/0.99  
% 2.09/0.99  fof(f42,plain,(
% 2.09/0.99    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f41,plain,(
% 2.09/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f43,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f72,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f43])).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1,negated_conjecture,
% 2.09/0.99      ( r1_tarski(sK4,X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_9,plain,
% 2.09/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_517,plain,
% 2.09/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | sK4 != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_518,plain,
% 2.09/0.99      ( ~ r2_hidden(X0,sK4) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_517]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2189,plain,
% 2.09/0.99      ( ~ r2_hidden(sK0(sK2,sK4),sK4) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_518]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6,negated_conjecture,
% 2.09/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1318,plain,
% 2.09/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.09/0.99      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1320,plain,
% 2.09/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 2.09/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1762,plain,
% 2.09/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK4))) = k3_subset_1(X0,sK4) ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1318,c_1320]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_0,negated_conjecture,
% 2.09/0.99      ( k1_setfam_1(k2_tarski(X0,sK4)) = sK4 ),
% 2.09/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2,negated_conjecture,
% 2.09/0.99      ( k5_xboole_0(X0,sK4) = X0 ),
% 2.09/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1767,plain,
% 2.09/0.99      ( k3_subset_1(X0,sK4) = X0 ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_1762,c_0,c_2]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_15,plain,
% 2.09/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.09/0.99      | ~ v3_pre_topc(X1,X0)
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.99      | ~ l1_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_22,negated_conjecture,
% 2.09/0.99      ( ~ v4_pre_topc(X0,sK2)
% 2.09/0.99      | ~ v3_pre_topc(X0,sK2)
% 2.09/0.99      | r2_hidden(X0,sK4)
% 2.09/0.99      | ~ r2_hidden(sK3,X0)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.09/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_451,plain,
% 2.09/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.09/0.99      | ~ v3_pre_topc(X2,sK2)
% 2.09/0.99      | r2_hidden(X2,sK4)
% 2.09/0.99      | ~ r2_hidden(sK3,X2)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | k3_subset_1(u1_struct_0(X1),X0) != X2
% 2.09/0.99      | sK2 != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_452,plain,
% 2.09/0.99      ( ~ v3_pre_topc(X0,sK2)
% 2.09/0.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
% 2.09/0.99      | r2_hidden(k3_subset_1(u1_struct_0(sK2),X0),sK4)
% 2.09/0.99      | ~ r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0))
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ l1_pre_topc(sK2) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_451]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_28,negated_conjecture,
% 2.09/0.99      ( l1_pre_topc(sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_456,plain,
% 2.09/0.99      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0))
% 2.09/0.99      | r2_hidden(k3_subset_1(u1_struct_0(sK2),X0),sK4)
% 2.09/0.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
% 2.09/0.99      | ~ v3_pre_topc(X0,sK2) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_452,c_28]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_457,plain,
% 2.09/0.99      ( ~ v3_pre_topc(X0,sK2)
% 2.09/0.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
% 2.09/0.99      | r2_hidden(k3_subset_1(u1_struct_0(sK2),X0),sK4)
% 2.09/0.99      | ~ r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0))
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_456]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_643,plain,
% 2.09/0.99      ( ~ v3_pre_topc(X0,sK2)
% 2.09/0.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2)
% 2.09/0.99      | ~ r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0))
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.09/0.99      inference(backward_subsumption_resolution,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_518,c_457]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1313,plain,
% 2.09/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.09/0.99      | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),X0),sK2) != iProver_top
% 2.09/0.99      | r2_hidden(sK3,k3_subset_1(u1_struct_0(sK2),X0)) != iProver_top
% 2.09/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.09/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK2),X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_11,plain,
% 2.09/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_10,plain,
% 2.09/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_363,plain,
% 2.09/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.09/0.99      inference(resolution,[status(thm)],[c_11,c_10]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_855,plain,
% 2.09/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_363,c_28]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_856,plain,
% 2.09/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_855]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1389,plain,
% 2.09/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 2.09/0.99      | v3_pre_topc(k3_subset_1(k2_struct_0(sK2),X0),sK2) != iProver_top
% 2.09/0.99      | r2_hidden(sK3,k3_subset_1(k2_struct_0(sK2),X0)) != iProver_top
% 2.09/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.09/0.99      | m1_subset_1(k3_subset_1(k2_struct_0(sK2),X0),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_1313,c_856]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2026,plain,
% 2.09/0.99      ( v3_pre_topc(k3_subset_1(k2_struct_0(sK2),sK4),sK2) != iProver_top
% 2.09/0.99      | v3_pre_topc(sK4,sK2) != iProver_top
% 2.09/0.99      | r2_hidden(sK3,k3_subset_1(k2_struct_0(sK2),sK4)) != iProver_top
% 2.09/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.09/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1767,c_1389]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2027,plain,
% 2.09/0.99      ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 2.09/0.99      | v3_pre_topc(sK4,sK2) != iProver_top
% 2.09/0.99      | r2_hidden(sK3,k2_struct_0(sK2)) != iProver_top
% 2.09/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.09/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.09/0.99      inference(demodulation,[status(thm)],[c_2026,c_1767]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_29,negated_conjecture,
% 2.09/0.99      ( v2_pre_topc(sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_32,plain,
% 2.09/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_33,plain,
% 2.09/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_13,plain,
% 2.09/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 2.09/0.99      | ~ v2_pre_topc(X0)
% 2.09/0.99      | ~ l1_pre_topc(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_80,plain,
% 2.09/0.99      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 2.09/0.99      | v2_pre_topc(X0) != iProver_top
% 2.09/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_82,plain,
% 2.09/0.99      ( v3_pre_topc(k2_struct_0(sK2),sK2) = iProver_top
% 2.09/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.09/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_80]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_27,negated_conjecture,
% 2.09/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1315,plain,
% 2.09/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1331,plain,
% 2.09/0.99      ( m1_subset_1(sK3,k2_struct_0(sK2)) = iProver_top ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_1315,c_856]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7,plain,
% 2.09/0.99      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_12,plain,
% 2.09/0.99      ( v2_struct_0(X0)
% 2.09/0.99      | ~ l1_struct_0(X0)
% 2.09/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_349,plain,
% 2.09/0.99      ( v2_struct_0(X0)
% 2.09/0.99      | ~ l1_pre_topc(X0)
% 2.09/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.09/0.99      inference(resolution,[status(thm)],[c_11,c_12]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_30,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_663,plain,
% 2.09/0.99      ( ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_349,c_30]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_664,plain,
% 2.09/0.99      ( ~ l1_pre_topc(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_663]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_84,plain,
% 2.09/0.99      ( v2_struct_0(sK2)
% 2.09/0.99      | ~ l1_struct_0(sK2)
% 2.09/0.99      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_87,plain,
% 2.09/0.99      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_666,plain,
% 2.09/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_664,c_30,c_28,c_84,c_87]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_827,plain,
% 2.09/0.99      ( r2_hidden(X0,X1)
% 2.09/0.99      | ~ m1_subset_1(X0,X1)
% 2.09/0.99      | u1_struct_0(sK2) != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_666]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_828,plain,
% 2.09/0.99      ( r2_hidden(X0,u1_struct_0(sK2))
% 2.09/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_827]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1309,plain,
% 2.09/0.99      ( r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
% 2.09/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1342,plain,
% 2.09/0.99      ( r2_hidden(X0,k2_struct_0(sK2)) = iProver_top
% 2.09/0.99      | m1_subset_1(X0,k2_struct_0(sK2)) != iProver_top ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_1309,c_856]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1621,plain,
% 2.09/0.99      ( r2_hidden(sK3,k2_struct_0(sK2)) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1331,c_1342]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2129,plain,
% 2.09/0.99      ( v3_pre_topc(sK4,sK2) != iProver_top
% 2.09/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.09/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_2027,c_32,c_33,c_82,c_1621]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5,plain,
% 2.09/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1319,plain,
% 2.09/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3,plain,
% 2.09/0.99      ( k2_subset_1(X0) = X0 ),
% 2.09/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1338,plain,
% 2.09/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_1319,c_3]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2136,plain,
% 2.09/0.99      ( v3_pre_topc(sK4,sK2) != iProver_top ),
% 2.09/0.99      inference(forward_subsumption_resolution,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_2129,c_1318,c_1338]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2137,plain,
% 2.09/0.99      ( ~ v3_pre_topc(sK4,sK2) ),
% 2.09/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2136]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_17,plain,
% 2.09/0.99      ( v3_pre_topc(X0,X1)
% 2.09/0.99      | r2_hidden(sK0(X1,X0),X0)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.99      | ~ v2_pre_topc(X1)
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | ~ l1_pre_topc(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_779,plain,
% 2.09/0.99      ( v3_pre_topc(X0,X1)
% 2.09/0.99      | r2_hidden(sK0(X1,X0),X0)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.99      | ~ v2_pre_topc(X1)
% 2.09/0.99      | ~ l1_pre_topc(X1)
% 2.09/0.99      | sK2 != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_780,plain,
% 2.09/0.99      ( v3_pre_topc(X0,sK2)
% 2.09/0.99      | r2_hidden(sK0(sK2,X0),X0)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.09/0.99      | ~ v2_pre_topc(sK2)
% 2.09/0.99      | ~ l1_pre_topc(sK2) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_779]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_784,plain,
% 2.09/0.99      ( v3_pre_topc(X0,sK2)
% 2.09/0.99      | r2_hidden(sK0(sK2,X0),X0)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_780,c_29,c_28]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1543,plain,
% 2.09/0.99      ( v3_pre_topc(sK4,sK2)
% 2.09/0.99      | r2_hidden(sK0(sK2,sK4),sK4)
% 2.09/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_784]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1460,plain,
% 2.09/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(contradiction,plain,
% 2.09/0.99      ( $false ),
% 2.09/0.99      inference(minisat,[status(thm)],[c_2189,c_2137,c_1543,c_1460]) ).
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  ------                               Statistics
% 2.09/0.99  
% 2.09/0.99  ------ General
% 2.09/0.99  
% 2.09/0.99  abstr_ref_over_cycles:                  0
% 2.09/0.99  abstr_ref_under_cycles:                 0
% 2.09/0.99  gc_basic_clause_elim:                   0
% 2.09/0.99  forced_gc_time:                         0
% 2.09/0.99  parsing_time:                           0.009
% 2.09/0.99  unif_index_cands_time:                  0.
% 2.09/0.99  unif_index_add_time:                    0.
% 2.09/0.99  orderings_time:                         0.
% 2.09/0.99  out_proof_time:                         0.01
% 2.09/0.99  total_time:                             0.101
% 2.09/0.99  num_of_symbols:                         55
% 2.09/0.99  num_of_terms:                           2140
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing
% 2.09/0.99  
% 2.09/0.99  num_of_splits:                          0
% 2.09/0.99  num_of_split_atoms:                     0
% 2.09/0.99  num_of_reused_defs:                     0
% 2.09/0.99  num_eq_ax_congr_red:                    25
% 2.09/0.99  num_of_sem_filtered_clauses:            1
% 2.09/0.99  num_of_subtypes:                        0
% 2.09/0.99  monotx_restored_types:                  0
% 2.09/0.99  sat_num_of_epr_types:                   0
% 2.09/0.99  sat_num_of_non_cyclic_types:            0
% 2.09/0.99  sat_guarded_non_collapsed_types:        0
% 2.09/0.99  num_pure_diseq_elim:                    0
% 2.09/0.99  simp_replaced_by:                       0
% 2.09/0.99  res_preprocessed:                       117
% 2.09/0.99  prep_upred:                             0
% 2.09/0.99  prep_unflattend:                        30
% 2.09/0.99  smt_new_axioms:                         0
% 2.09/0.99  pred_elim_cands:                        3
% 2.09/0.99  pred_elim:                              8
% 2.09/0.99  pred_elim_cl:                           12
% 2.09/0.99  pred_elim_cycles:                       13
% 2.09/0.99  merged_defs:                            0
% 2.09/0.99  merged_defs_ncl:                        0
% 2.09/0.99  bin_hyper_res:                          0
% 2.09/0.99  prep_cycles:                            4
% 2.09/0.99  pred_elim_time:                         0.014
% 2.09/0.99  splitting_time:                         0.
% 2.09/0.99  sem_filter_time:                        0.
% 2.09/0.99  monotx_time:                            0.
% 2.09/0.99  subtype_inf_time:                       0.
% 2.09/0.99  
% 2.09/0.99  ------ Problem properties
% 2.09/0.99  
% 2.09/0.99  clauses:                                19
% 2.09/0.99  conjectures:                            5
% 2.09/0.99  epr:                                    1
% 2.09/0.99  horn:                                   17
% 2.09/0.99  ground:                                 4
% 2.09/0.99  unary:                                  10
% 2.09/0.99  binary:                                 2
% 2.09/0.99  lits:                                   42
% 2.09/0.99  lits_eq:                                6
% 2.09/0.99  fd_pure:                                0
% 2.09/0.99  fd_pseudo:                              0
% 2.09/0.99  fd_cond:                                0
% 2.09/0.99  fd_pseudo_cond:                         0
% 2.09/0.99  ac_symbols:                             0
% 2.09/0.99  
% 2.09/0.99  ------ Propositional Solver
% 2.09/0.99  
% 2.09/0.99  prop_solver_calls:                      25
% 2.09/0.99  prop_fast_solver_calls:                 786
% 2.09/0.99  smt_solver_calls:                       0
% 2.09/0.99  smt_fast_solver_calls:                  0
% 2.09/0.99  prop_num_of_clauses:                    685
% 2.09/0.99  prop_preprocess_simplified:             3437
% 2.09/0.99  prop_fo_subsumed:                       16
% 2.09/0.99  prop_solver_time:                       0.
% 2.09/0.99  smt_solver_time:                        0.
% 2.09/0.99  smt_fast_solver_time:                   0.
% 2.09/0.99  prop_fast_solver_time:                  0.
% 2.09/0.99  prop_unsat_core_time:                   0.
% 2.09/0.99  
% 2.09/0.99  ------ QBF
% 2.09/0.99  
% 2.09/0.99  qbf_q_res:                              0
% 2.09/0.99  qbf_num_tautologies:                    0
% 2.09/0.99  qbf_prep_cycles:                        0
% 2.09/0.99  
% 2.09/0.99  ------ BMC1
% 2.09/0.99  
% 2.09/0.99  bmc1_current_bound:                     -1
% 2.09/0.99  bmc1_last_solved_bound:                 -1
% 2.09/0.99  bmc1_unsat_core_size:                   -1
% 2.09/0.99  bmc1_unsat_core_parents_size:           -1
% 2.09/0.99  bmc1_merge_next_fun:                    0
% 2.09/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation
% 2.09/0.99  
% 2.09/0.99  inst_num_of_clauses:                    161
% 2.09/0.99  inst_num_in_passive:                    48
% 2.09/0.99  inst_num_in_active:                     89
% 2.09/0.99  inst_num_in_unprocessed:                23
% 2.09/0.99  inst_num_of_loops:                      94
% 2.09/0.99  inst_num_of_learning_restarts:          0
% 2.09/0.99  inst_num_moves_active_passive:          2
% 2.09/0.99  inst_lit_activity:                      0
% 2.09/0.99  inst_lit_activity_moves:                0
% 2.09/0.99  inst_num_tautologies:                   0
% 2.09/0.99  inst_num_prop_implied:                  0
% 2.09/0.99  inst_num_existing_simplified:           0
% 2.09/0.99  inst_num_eq_res_simplified:             0
% 2.09/0.99  inst_num_child_elim:                    0
% 2.09/0.99  inst_num_of_dismatching_blockings:      9
% 2.09/0.99  inst_num_of_non_proper_insts:           89
% 2.09/0.99  inst_num_of_duplicates:                 0
% 2.09/0.99  inst_inst_num_from_inst_to_res:         0
% 2.09/0.99  inst_dismatching_checking_time:         0.
% 2.09/0.99  
% 2.09/0.99  ------ Resolution
% 2.09/0.99  
% 2.09/0.99  res_num_of_clauses:                     0
% 2.09/0.99  res_num_in_passive:                     0
% 2.09/0.99  res_num_in_active:                      0
% 2.09/0.99  res_num_of_loops:                       121
% 2.09/0.99  res_forward_subset_subsumed:            9
% 2.09/0.99  res_backward_subset_subsumed:           1
% 2.09/0.99  res_forward_subsumed:                   0
% 2.09/0.99  res_backward_subsumed:                  2
% 2.09/0.99  res_forward_subsumption_resolution:     6
% 2.09/0.99  res_backward_subsumption_resolution:    1
% 2.09/0.99  res_clause_to_clause_subsumption:       153
% 2.09/0.99  res_orphan_elimination:                 0
% 2.09/0.99  res_tautology_del:                      7
% 2.09/0.99  res_num_eq_res_simplified:              0
% 2.09/0.99  res_num_sel_changes:                    0
% 2.09/0.99  res_moves_from_active_to_pass:          0
% 2.09/0.99  
% 2.09/0.99  ------ Superposition
% 2.09/0.99  
% 2.09/0.99  sup_time_total:                         0.
% 2.09/0.99  sup_time_generating:                    0.
% 2.09/0.99  sup_time_sim_full:                      0.
% 2.09/0.99  sup_time_sim_immed:                     0.
% 2.09/0.99  
% 2.09/0.99  sup_num_of_clauses:                     25
% 2.09/0.99  sup_num_in_active:                      18
% 2.09/0.99  sup_num_in_passive:                     7
% 2.09/0.99  sup_num_of_loops:                       18
% 2.09/0.99  sup_fw_superposition:                   5
% 2.09/0.99  sup_bw_superposition:                   3
% 2.09/0.99  sup_immediate_simplified:               3
% 2.09/0.99  sup_given_eliminated:                   0
% 2.09/0.99  comparisons_done:                       0
% 2.09/0.99  comparisons_avoided:                    0
% 2.09/0.99  
% 2.09/0.99  ------ Simplifications
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  sim_fw_subset_subsumed:                 1
% 2.09/0.99  sim_bw_subset_subsumed:                 0
% 2.09/0.99  sim_fw_subsumed:                        1
% 2.09/0.99  sim_bw_subsumed:                        0
% 2.09/0.99  sim_fw_subsumption_res:                 2
% 2.09/0.99  sim_bw_subsumption_res:                 0
% 2.09/0.99  sim_tautology_del:                      0
% 2.09/0.99  sim_eq_tautology_del:                   0
% 2.09/0.99  sim_eq_res_simp:                        0
% 2.09/0.99  sim_fw_demodulated:                     1
% 2.09/0.99  sim_bw_demodulated:                     0
% 2.09/0.99  sim_light_normalised:                   11
% 2.09/0.99  sim_joinable_taut:                      0
% 2.09/0.99  sim_joinable_simp:                      0
% 2.09/0.99  sim_ac_normalised:                      0
% 2.09/0.99  sim_smt_subsumption:                    0
% 2.09/0.99  
%------------------------------------------------------------------------------
