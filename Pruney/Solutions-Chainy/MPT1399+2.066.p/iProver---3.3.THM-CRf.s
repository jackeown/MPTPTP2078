%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:44 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 362 expanded)
%              Number of clauses        :   61 (  98 expanded)
%              Number of leaves         :   17 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          :  392 (3175 expanded)
%              Number of equality atoms :   79 ( 323 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f34,plain,(
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
     => ( k1_xboole_0 = sK3
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK3) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                    | ~ r2_hidden(sK2,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK2,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
                      | ~ v4_pre_topc(X3,sK1)
                      | ~ v3_pre_topc(X3,sK1) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK1)
                        & v3_pre_topc(X3,sK1) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_xboole_0 = sK3
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK3)
            | ~ r2_hidden(sK2,X3)
            | ~ v4_pre_topc(X3,sK1)
            | ~ v3_pre_topc(X3,sK1) )
          & ( ( r2_hidden(sK2,X3)
              & v4_pre_topc(X3,sK1)
              & v3_pre_topc(X3,sK1) )
            | ~ r2_hidden(X3,sK3) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).

fof(f54,plain,(
    ! [X3] :
      ( r2_hidden(sK2,X3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | ~ r2_hidden(sK2,X3)
      | ~ v4_pre_topc(X3,sK1)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK0) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f28])).

fof(f37,plain,(
    v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1110,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1127,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1110,c_2])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1107,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_229,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_269,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_229,c_18])).

cnf(c_270,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_1149,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1107,c_11,c_270])).

cnf(c_1564,plain,
    ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1149])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_216,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_217,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_45,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_48,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_219,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_217,c_20,c_18,c_45,c_48])).

cnf(c_1104,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_1121,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1104,c_270])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1105,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1124,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1105,c_270])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1109,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1646,plain,
    ( r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_1109])).

cnf(c_1749,plain,
    ( r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1564,c_1121,c_1646])).

cnf(c_12,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_254,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_255,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_42,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_257,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_19,c_18,c_42])).

cnf(c_276,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_struct_0(sK1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_257])).

cnf(c_277,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
    | r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_10,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_39,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_279,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_19,c_18,c_39])).

cnf(c_1103,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_1156,plain,
    ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1103,c_11,c_270])).

cnf(c_1160,plain,
    ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1156,c_1127])).

cnf(c_1754,plain,
    ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1160])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1108,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1563,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1108])).

cnf(c_1914,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_1563])).

cnf(c_908,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1222,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0)
    | X0 != sK0 ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_1284,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_1285,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1284])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_297,plain,
    ( sK0 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_298,plain,
    ( k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_63,plain,
    ( v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1914,c_1285,c_298,c_63])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:20:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.33/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.33/1.05  
% 1.33/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.33/1.05  
% 1.33/1.05  ------  iProver source info
% 1.33/1.05  
% 1.33/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.33/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.33/1.05  git: non_committed_changes: false
% 1.33/1.05  git: last_make_outside_of_git: false
% 1.33/1.05  
% 1.33/1.05  ------ 
% 1.33/1.05  
% 1.33/1.05  ------ Input Options
% 1.33/1.05  
% 1.33/1.05  --out_options                           all
% 1.33/1.05  --tptp_safe_out                         true
% 1.33/1.05  --problem_path                          ""
% 1.33/1.05  --include_path                          ""
% 1.33/1.05  --clausifier                            res/vclausify_rel
% 1.33/1.05  --clausifier_options                    --mode clausify
% 1.33/1.05  --stdin                                 false
% 1.33/1.05  --stats_out                             all
% 1.33/1.05  
% 1.33/1.05  ------ General Options
% 1.33/1.05  
% 1.33/1.05  --fof                                   false
% 1.33/1.05  --time_out_real                         305.
% 1.33/1.05  --time_out_virtual                      -1.
% 1.33/1.05  --symbol_type_check                     false
% 1.33/1.05  --clausify_out                          false
% 1.33/1.05  --sig_cnt_out                           false
% 1.33/1.05  --trig_cnt_out                          false
% 1.33/1.05  --trig_cnt_out_tolerance                1.
% 1.33/1.05  --trig_cnt_out_sk_spl                   false
% 1.33/1.05  --abstr_cl_out                          false
% 1.33/1.05  
% 1.33/1.05  ------ Global Options
% 1.33/1.05  
% 1.33/1.05  --schedule                              default
% 1.33/1.05  --add_important_lit                     false
% 1.33/1.05  --prop_solver_per_cl                    1000
% 1.33/1.05  --min_unsat_core                        false
% 1.33/1.05  --soft_assumptions                      false
% 1.33/1.05  --soft_lemma_size                       3
% 1.33/1.05  --prop_impl_unit_size                   0
% 1.33/1.05  --prop_impl_unit                        []
% 1.33/1.05  --share_sel_clauses                     true
% 1.33/1.05  --reset_solvers                         false
% 1.33/1.05  --bc_imp_inh                            [conj_cone]
% 1.33/1.05  --conj_cone_tolerance                   3.
% 1.33/1.05  --extra_neg_conj                        none
% 1.33/1.05  --large_theory_mode                     true
% 1.33/1.05  --prolific_symb_bound                   200
% 1.33/1.05  --lt_threshold                          2000
% 1.33/1.05  --clause_weak_htbl                      true
% 1.33/1.05  --gc_record_bc_elim                     false
% 1.33/1.05  
% 1.33/1.05  ------ Preprocessing Options
% 1.33/1.05  
% 1.33/1.05  --preprocessing_flag                    true
% 1.33/1.05  --time_out_prep_mult                    0.1
% 1.33/1.05  --splitting_mode                        input
% 1.33/1.05  --splitting_grd                         true
% 1.33/1.05  --splitting_cvd                         false
% 1.33/1.05  --splitting_cvd_svl                     false
% 1.33/1.05  --splitting_nvd                         32
% 1.33/1.05  --sub_typing                            true
% 1.33/1.05  --prep_gs_sim                           true
% 1.33/1.05  --prep_unflatten                        true
% 1.33/1.05  --prep_res_sim                          true
% 1.33/1.05  --prep_upred                            true
% 1.33/1.05  --prep_sem_filter                       exhaustive
% 1.33/1.05  --prep_sem_filter_out                   false
% 1.33/1.05  --pred_elim                             true
% 1.33/1.05  --res_sim_input                         true
% 1.33/1.05  --eq_ax_congr_red                       true
% 1.33/1.05  --pure_diseq_elim                       true
% 1.33/1.05  --brand_transform                       false
% 1.33/1.05  --non_eq_to_eq                          false
% 1.33/1.05  --prep_def_merge                        true
% 1.33/1.05  --prep_def_merge_prop_impl              false
% 1.33/1.05  --prep_def_merge_mbd                    true
% 1.33/1.05  --prep_def_merge_tr_red                 false
% 1.33/1.05  --prep_def_merge_tr_cl                  false
% 1.33/1.05  --smt_preprocessing                     true
% 1.33/1.05  --smt_ac_axioms                         fast
% 1.33/1.05  --preprocessed_out                      false
% 1.33/1.05  --preprocessed_stats                    false
% 1.33/1.05  
% 1.33/1.05  ------ Abstraction refinement Options
% 1.33/1.05  
% 1.33/1.05  --abstr_ref                             []
% 1.33/1.05  --abstr_ref_prep                        false
% 1.33/1.05  --abstr_ref_until_sat                   false
% 1.33/1.05  --abstr_ref_sig_restrict                funpre
% 1.33/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/1.05  --abstr_ref_under                       []
% 1.33/1.05  
% 1.33/1.05  ------ SAT Options
% 1.33/1.05  
% 1.33/1.05  --sat_mode                              false
% 1.33/1.05  --sat_fm_restart_options                ""
% 1.33/1.05  --sat_gr_def                            false
% 1.33/1.05  --sat_epr_types                         true
% 1.33/1.05  --sat_non_cyclic_types                  false
% 1.33/1.05  --sat_finite_models                     false
% 1.33/1.05  --sat_fm_lemmas                         false
% 1.33/1.05  --sat_fm_prep                           false
% 1.33/1.05  --sat_fm_uc_incr                        true
% 1.33/1.05  --sat_out_model                         small
% 1.33/1.05  --sat_out_clauses                       false
% 1.33/1.05  
% 1.33/1.05  ------ QBF Options
% 1.33/1.05  
% 1.33/1.05  --qbf_mode                              false
% 1.33/1.05  --qbf_elim_univ                         false
% 1.33/1.05  --qbf_dom_inst                          none
% 1.33/1.05  --qbf_dom_pre_inst                      false
% 1.33/1.05  --qbf_sk_in                             false
% 1.33/1.05  --qbf_pred_elim                         true
% 1.33/1.05  --qbf_split                             512
% 1.33/1.05  
% 1.33/1.05  ------ BMC1 Options
% 1.33/1.05  
% 1.33/1.05  --bmc1_incremental                      false
% 1.33/1.05  --bmc1_axioms                           reachable_all
% 1.33/1.05  --bmc1_min_bound                        0
% 1.33/1.05  --bmc1_max_bound                        -1
% 1.33/1.05  --bmc1_max_bound_default                -1
% 1.33/1.05  --bmc1_symbol_reachability              true
% 1.33/1.05  --bmc1_property_lemmas                  false
% 1.33/1.05  --bmc1_k_induction                      false
% 1.33/1.05  --bmc1_non_equiv_states                 false
% 1.33/1.05  --bmc1_deadlock                         false
% 1.33/1.05  --bmc1_ucm                              false
% 1.33/1.05  --bmc1_add_unsat_core                   none
% 1.33/1.05  --bmc1_unsat_core_children              false
% 1.33/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/1.05  --bmc1_out_stat                         full
% 1.33/1.05  --bmc1_ground_init                      false
% 1.33/1.05  --bmc1_pre_inst_next_state              false
% 1.33/1.05  --bmc1_pre_inst_state                   false
% 1.33/1.05  --bmc1_pre_inst_reach_state             false
% 1.33/1.05  --bmc1_out_unsat_core                   false
% 1.33/1.05  --bmc1_aig_witness_out                  false
% 1.33/1.05  --bmc1_verbose                          false
% 1.33/1.05  --bmc1_dump_clauses_tptp                false
% 1.33/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.33/1.05  --bmc1_dump_file                        -
% 1.33/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.33/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.33/1.05  --bmc1_ucm_extend_mode                  1
% 1.33/1.05  --bmc1_ucm_init_mode                    2
% 1.33/1.05  --bmc1_ucm_cone_mode                    none
% 1.33/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.33/1.05  --bmc1_ucm_relax_model                  4
% 1.33/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.33/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/1.05  --bmc1_ucm_layered_model                none
% 1.33/1.05  --bmc1_ucm_max_lemma_size               10
% 1.33/1.05  
% 1.33/1.05  ------ AIG Options
% 1.33/1.05  
% 1.33/1.05  --aig_mode                              false
% 1.33/1.05  
% 1.33/1.05  ------ Instantiation Options
% 1.33/1.05  
% 1.33/1.05  --instantiation_flag                    true
% 1.33/1.05  --inst_sos_flag                         false
% 1.33/1.05  --inst_sos_phase                        true
% 1.33/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/1.05  --inst_lit_sel_side                     num_symb
% 1.33/1.05  --inst_solver_per_active                1400
% 1.33/1.05  --inst_solver_calls_frac                1.
% 1.33/1.05  --inst_passive_queue_type               priority_queues
% 1.33/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.33/1.05  --inst_passive_queues_freq              [25;2]
% 1.33/1.05  --inst_dismatching                      true
% 1.33/1.05  --inst_eager_unprocessed_to_passive     true
% 1.33/1.05  --inst_prop_sim_given                   true
% 1.33/1.05  --inst_prop_sim_new                     false
% 1.33/1.05  --inst_subs_new                         false
% 1.33/1.05  --inst_eq_res_simp                      false
% 1.33/1.05  --inst_subs_given                       false
% 1.33/1.05  --inst_orphan_elimination               true
% 1.33/1.05  --inst_learning_loop_flag               true
% 1.33/1.05  --inst_learning_start                   3000
% 1.33/1.05  --inst_learning_factor                  2
% 1.33/1.05  --inst_start_prop_sim_after_learn       3
% 1.33/1.05  --inst_sel_renew                        solver
% 1.33/1.05  --inst_lit_activity_flag                true
% 1.33/1.05  --inst_restr_to_given                   false
% 1.33/1.05  --inst_activity_threshold               500
% 1.33/1.05  --inst_out_proof                        true
% 1.33/1.05  
% 1.33/1.05  ------ Resolution Options
% 1.33/1.05  
% 1.33/1.05  --resolution_flag                       true
% 1.33/1.05  --res_lit_sel                           adaptive
% 1.33/1.05  --res_lit_sel_side                      none
% 1.33/1.05  --res_ordering                          kbo
% 1.33/1.05  --res_to_prop_solver                    active
% 1.33/1.05  --res_prop_simpl_new                    false
% 1.33/1.05  --res_prop_simpl_given                  true
% 1.33/1.05  --res_passive_queue_type                priority_queues
% 1.33/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.33/1.05  --res_passive_queues_freq               [15;5]
% 1.33/1.05  --res_forward_subs                      full
% 1.33/1.05  --res_backward_subs                     full
% 1.33/1.05  --res_forward_subs_resolution           true
% 1.33/1.05  --res_backward_subs_resolution          true
% 1.33/1.05  --res_orphan_elimination                true
% 1.33/1.05  --res_time_limit                        2.
% 1.33/1.05  --res_out_proof                         true
% 1.33/1.05  
% 1.33/1.05  ------ Superposition Options
% 1.33/1.05  
% 1.33/1.05  --superposition_flag                    true
% 1.33/1.05  --sup_passive_queue_type                priority_queues
% 1.33/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.33/1.05  --demod_completeness_check              fast
% 1.33/1.05  --demod_use_ground                      true
% 1.33/1.05  --sup_to_prop_solver                    passive
% 1.33/1.05  --sup_prop_simpl_new                    true
% 1.33/1.05  --sup_prop_simpl_given                  true
% 1.33/1.05  --sup_fun_splitting                     false
% 1.33/1.05  --sup_smt_interval                      50000
% 1.33/1.05  
% 1.33/1.05  ------ Superposition Simplification Setup
% 1.33/1.05  
% 1.33/1.05  --sup_indices_passive                   []
% 1.33/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.05  --sup_full_bw                           [BwDemod]
% 1.33/1.05  --sup_immed_triv                        [TrivRules]
% 1.33/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.05  --sup_immed_bw_main                     []
% 1.33/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/1.05  
% 1.33/1.05  ------ Combination Options
% 1.33/1.05  
% 1.33/1.05  --comb_res_mult                         3
% 1.33/1.05  --comb_sup_mult                         2
% 1.33/1.05  --comb_inst_mult                        10
% 1.33/1.05  
% 1.33/1.05  ------ Debug Options
% 1.33/1.05  
% 1.33/1.05  --dbg_backtrace                         false
% 1.33/1.05  --dbg_dump_prop_clauses                 false
% 1.33/1.05  --dbg_dump_prop_clauses_file            -
% 1.33/1.05  --dbg_out_stat                          false
% 1.33/1.05  ------ Parsing...
% 1.33/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.33/1.05  
% 1.33/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.33/1.05  
% 1.33/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.33/1.05  
% 1.33/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.33/1.05  ------ Proving...
% 1.33/1.05  ------ Problem Properties 
% 1.33/1.05  
% 1.33/1.05  
% 1.33/1.05  clauses                                 13
% 1.33/1.05  conjectures                             4
% 1.33/1.05  EPR                                     4
% 1.33/1.05  Horn                                    12
% 1.33/1.05  unary                                   8
% 1.33/1.05  binary                                  1
% 1.33/1.05  lits                                    22
% 1.33/1.05  lits eq                                 4
% 1.33/1.05  fd_pure                                 0
% 1.33/1.05  fd_pseudo                               0
% 1.33/1.05  fd_cond                                 1
% 1.33/1.05  fd_pseudo_cond                          0
% 1.33/1.05  AC symbols                              0
% 1.33/1.05  
% 1.33/1.05  ------ Schedule dynamic 5 is on 
% 1.33/1.05  
% 1.33/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.33/1.05  
% 1.33/1.05  
% 1.33/1.05  ------ 
% 1.33/1.05  Current options:
% 1.33/1.05  ------ 
% 1.33/1.05  
% 1.33/1.05  ------ Input Options
% 1.33/1.05  
% 1.33/1.05  --out_options                           all
% 1.33/1.05  --tptp_safe_out                         true
% 1.33/1.05  --problem_path                          ""
% 1.33/1.05  --include_path                          ""
% 1.33/1.05  --clausifier                            res/vclausify_rel
% 1.33/1.05  --clausifier_options                    --mode clausify
% 1.33/1.05  --stdin                                 false
% 1.33/1.05  --stats_out                             all
% 1.33/1.05  
% 1.33/1.05  ------ General Options
% 1.33/1.05  
% 1.33/1.05  --fof                                   false
% 1.33/1.05  --time_out_real                         305.
% 1.33/1.05  --time_out_virtual                      -1.
% 1.33/1.05  --symbol_type_check                     false
% 1.33/1.05  --clausify_out                          false
% 1.33/1.05  --sig_cnt_out                           false
% 1.33/1.05  --trig_cnt_out                          false
% 1.33/1.05  --trig_cnt_out_tolerance                1.
% 1.33/1.05  --trig_cnt_out_sk_spl                   false
% 1.33/1.05  --abstr_cl_out                          false
% 1.33/1.05  
% 1.33/1.05  ------ Global Options
% 1.33/1.05  
% 1.33/1.05  --schedule                              default
% 1.33/1.05  --add_important_lit                     false
% 1.33/1.05  --prop_solver_per_cl                    1000
% 1.33/1.05  --min_unsat_core                        false
% 1.33/1.05  --soft_assumptions                      false
% 1.33/1.05  --soft_lemma_size                       3
% 1.33/1.05  --prop_impl_unit_size                   0
% 1.33/1.05  --prop_impl_unit                        []
% 1.33/1.05  --share_sel_clauses                     true
% 1.33/1.05  --reset_solvers                         false
% 1.33/1.05  --bc_imp_inh                            [conj_cone]
% 1.33/1.05  --conj_cone_tolerance                   3.
% 1.33/1.05  --extra_neg_conj                        none
% 1.33/1.05  --large_theory_mode                     true
% 1.33/1.05  --prolific_symb_bound                   200
% 1.33/1.05  --lt_threshold                          2000
% 1.33/1.05  --clause_weak_htbl                      true
% 1.33/1.05  --gc_record_bc_elim                     false
% 1.33/1.05  
% 1.33/1.05  ------ Preprocessing Options
% 1.33/1.05  
% 1.33/1.05  --preprocessing_flag                    true
% 1.33/1.05  --time_out_prep_mult                    0.1
% 1.33/1.05  --splitting_mode                        input
% 1.33/1.05  --splitting_grd                         true
% 1.33/1.05  --splitting_cvd                         false
% 1.33/1.05  --splitting_cvd_svl                     false
% 1.33/1.05  --splitting_nvd                         32
% 1.33/1.05  --sub_typing                            true
% 1.33/1.05  --prep_gs_sim                           true
% 1.33/1.05  --prep_unflatten                        true
% 1.33/1.05  --prep_res_sim                          true
% 1.33/1.05  --prep_upred                            true
% 1.33/1.05  --prep_sem_filter                       exhaustive
% 1.33/1.05  --prep_sem_filter_out                   false
% 1.33/1.05  --pred_elim                             true
% 1.33/1.05  --res_sim_input                         true
% 1.33/1.05  --eq_ax_congr_red                       true
% 1.33/1.05  --pure_diseq_elim                       true
% 1.33/1.05  --brand_transform                       false
% 1.33/1.05  --non_eq_to_eq                          false
% 1.33/1.05  --prep_def_merge                        true
% 1.33/1.05  --prep_def_merge_prop_impl              false
% 1.33/1.05  --prep_def_merge_mbd                    true
% 1.33/1.05  --prep_def_merge_tr_red                 false
% 1.33/1.05  --prep_def_merge_tr_cl                  false
% 1.33/1.05  --smt_preprocessing                     true
% 1.33/1.05  --smt_ac_axioms                         fast
% 1.33/1.05  --preprocessed_out                      false
% 1.33/1.05  --preprocessed_stats                    false
% 1.33/1.05  
% 1.33/1.05  ------ Abstraction refinement Options
% 1.33/1.05  
% 1.33/1.05  --abstr_ref                             []
% 1.33/1.05  --abstr_ref_prep                        false
% 1.33/1.05  --abstr_ref_until_sat                   false
% 1.33/1.05  --abstr_ref_sig_restrict                funpre
% 1.33/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/1.05  --abstr_ref_under                       []
% 1.33/1.05  
% 1.33/1.05  ------ SAT Options
% 1.33/1.05  
% 1.33/1.05  --sat_mode                              false
% 1.33/1.05  --sat_fm_restart_options                ""
% 1.33/1.05  --sat_gr_def                            false
% 1.33/1.05  --sat_epr_types                         true
% 1.33/1.05  --sat_non_cyclic_types                  false
% 1.33/1.05  --sat_finite_models                     false
% 1.33/1.05  --sat_fm_lemmas                         false
% 1.33/1.05  --sat_fm_prep                           false
% 1.33/1.05  --sat_fm_uc_incr                        true
% 1.33/1.05  --sat_out_model                         small
% 1.33/1.05  --sat_out_clauses                       false
% 1.33/1.05  
% 1.33/1.05  ------ QBF Options
% 1.33/1.05  
% 1.33/1.05  --qbf_mode                              false
% 1.33/1.05  --qbf_elim_univ                         false
% 1.33/1.05  --qbf_dom_inst                          none
% 1.33/1.05  --qbf_dom_pre_inst                      false
% 1.33/1.05  --qbf_sk_in                             false
% 1.33/1.05  --qbf_pred_elim                         true
% 1.33/1.05  --qbf_split                             512
% 1.33/1.05  
% 1.33/1.05  ------ BMC1 Options
% 1.33/1.05  
% 1.33/1.05  --bmc1_incremental                      false
% 1.33/1.05  --bmc1_axioms                           reachable_all
% 1.33/1.05  --bmc1_min_bound                        0
% 1.33/1.05  --bmc1_max_bound                        -1
% 1.33/1.05  --bmc1_max_bound_default                -1
% 1.33/1.05  --bmc1_symbol_reachability              true
% 1.33/1.05  --bmc1_property_lemmas                  false
% 1.33/1.05  --bmc1_k_induction                      false
% 1.33/1.05  --bmc1_non_equiv_states                 false
% 1.33/1.05  --bmc1_deadlock                         false
% 1.33/1.05  --bmc1_ucm                              false
% 1.33/1.05  --bmc1_add_unsat_core                   none
% 1.33/1.05  --bmc1_unsat_core_children              false
% 1.33/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/1.05  --bmc1_out_stat                         full
% 1.33/1.05  --bmc1_ground_init                      false
% 1.33/1.05  --bmc1_pre_inst_next_state              false
% 1.33/1.05  --bmc1_pre_inst_state                   false
% 1.33/1.05  --bmc1_pre_inst_reach_state             false
% 1.33/1.05  --bmc1_out_unsat_core                   false
% 1.33/1.05  --bmc1_aig_witness_out                  false
% 1.33/1.05  --bmc1_verbose                          false
% 1.33/1.05  --bmc1_dump_clauses_tptp                false
% 1.33/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.33/1.05  --bmc1_dump_file                        -
% 1.33/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.33/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.33/1.05  --bmc1_ucm_extend_mode                  1
% 1.33/1.05  --bmc1_ucm_init_mode                    2
% 1.33/1.05  --bmc1_ucm_cone_mode                    none
% 1.33/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.33/1.05  --bmc1_ucm_relax_model                  4
% 1.33/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.33/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/1.05  --bmc1_ucm_layered_model                none
% 1.33/1.05  --bmc1_ucm_max_lemma_size               10
% 1.33/1.05  
% 1.33/1.05  ------ AIG Options
% 1.33/1.05  
% 1.33/1.05  --aig_mode                              false
% 1.33/1.05  
% 1.33/1.05  ------ Instantiation Options
% 1.33/1.05  
% 1.33/1.05  --instantiation_flag                    true
% 1.33/1.05  --inst_sos_flag                         false
% 1.33/1.05  --inst_sos_phase                        true
% 1.33/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/1.05  --inst_lit_sel_side                     none
% 1.33/1.05  --inst_solver_per_active                1400
% 1.33/1.05  --inst_solver_calls_frac                1.
% 1.33/1.05  --inst_passive_queue_type               priority_queues
% 1.33/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.33/1.05  --inst_passive_queues_freq              [25;2]
% 1.33/1.05  --inst_dismatching                      true
% 1.33/1.05  --inst_eager_unprocessed_to_passive     true
% 1.33/1.05  --inst_prop_sim_given                   true
% 1.33/1.05  --inst_prop_sim_new                     false
% 1.33/1.05  --inst_subs_new                         false
% 1.33/1.05  --inst_eq_res_simp                      false
% 1.33/1.05  --inst_subs_given                       false
% 1.33/1.05  --inst_orphan_elimination               true
% 1.33/1.05  --inst_learning_loop_flag               true
% 1.33/1.05  --inst_learning_start                   3000
% 1.33/1.05  --inst_learning_factor                  2
% 1.33/1.05  --inst_start_prop_sim_after_learn       3
% 1.33/1.05  --inst_sel_renew                        solver
% 1.33/1.05  --inst_lit_activity_flag                true
% 1.33/1.05  --inst_restr_to_given                   false
% 1.33/1.05  --inst_activity_threshold               500
% 1.33/1.05  --inst_out_proof                        true
% 1.33/1.05  
% 1.33/1.05  ------ Resolution Options
% 1.33/1.05  
% 1.33/1.05  --resolution_flag                       false
% 1.33/1.05  --res_lit_sel                           adaptive
% 1.33/1.05  --res_lit_sel_side                      none
% 1.33/1.05  --res_ordering                          kbo
% 1.33/1.05  --res_to_prop_solver                    active
% 1.33/1.05  --res_prop_simpl_new                    false
% 1.33/1.05  --res_prop_simpl_given                  true
% 1.33/1.05  --res_passive_queue_type                priority_queues
% 1.33/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.33/1.05  --res_passive_queues_freq               [15;5]
% 1.33/1.05  --res_forward_subs                      full
% 1.33/1.05  --res_backward_subs                     full
% 1.33/1.05  --res_forward_subs_resolution           true
% 1.33/1.05  --res_backward_subs_resolution          true
% 1.33/1.05  --res_orphan_elimination                true
% 1.33/1.05  --res_time_limit                        2.
% 1.33/1.05  --res_out_proof                         true
% 1.33/1.05  
% 1.33/1.05  ------ Superposition Options
% 1.33/1.05  
% 1.33/1.05  --superposition_flag                    true
% 1.33/1.05  --sup_passive_queue_type                priority_queues
% 1.33/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.33/1.05  --demod_completeness_check              fast
% 1.33/1.05  --demod_use_ground                      true
% 1.33/1.05  --sup_to_prop_solver                    passive
% 1.33/1.05  --sup_prop_simpl_new                    true
% 1.33/1.05  --sup_prop_simpl_given                  true
% 1.33/1.05  --sup_fun_splitting                     false
% 1.33/1.05  --sup_smt_interval                      50000
% 1.33/1.05  
% 1.33/1.05  ------ Superposition Simplification Setup
% 1.33/1.05  
% 1.33/1.05  --sup_indices_passive                   []
% 1.33/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.05  --sup_full_bw                           [BwDemod]
% 1.33/1.05  --sup_immed_triv                        [TrivRules]
% 1.33/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.05  --sup_immed_bw_main                     []
% 1.33/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/1.05  
% 1.33/1.05  ------ Combination Options
% 1.33/1.05  
% 1.33/1.05  --comb_res_mult                         3
% 1.33/1.05  --comb_sup_mult                         2
% 1.33/1.05  --comb_inst_mult                        10
% 1.33/1.05  
% 1.33/1.05  ------ Debug Options
% 1.33/1.05  
% 1.33/1.05  --dbg_backtrace                         false
% 1.33/1.05  --dbg_dump_prop_clauses                 false
% 1.33/1.05  --dbg_dump_prop_clauses_file            -
% 1.33/1.05  --dbg_out_stat                          false
% 1.33/1.05  
% 1.33/1.05  
% 1.33/1.05  
% 1.33/1.05  
% 1.33/1.05  ------ Proving...
% 1.33/1.05  
% 1.33/1.05  
% 1.33/1.05  % SZS status Theorem for theBenchmark.p
% 1.33/1.05  
% 1.33/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.33/1.05  
% 1.33/1.05  fof(f4,axiom,(
% 1.33/1.05    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f39,plain,(
% 1.33/1.05    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.33/1.05    inference(cnf_transformation,[],[f4])).
% 1.33/1.05  
% 1.33/1.05  fof(f3,axiom,(
% 1.33/1.05    ! [X0] : k2_subset_1(X0) = X0),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f38,plain,(
% 1.33/1.05    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.33/1.05    inference(cnf_transformation,[],[f3])).
% 1.33/1.05  
% 1.33/1.05  fof(f12,conjecture,(
% 1.33/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f13,negated_conjecture,(
% 1.33/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.33/1.05    inference(negated_conjecture,[],[f12])).
% 1.33/1.05  
% 1.33/1.05  fof(f26,plain,(
% 1.33/1.05    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.33/1.05    inference(ennf_transformation,[],[f13])).
% 1.33/1.05  
% 1.33/1.05  fof(f27,plain,(
% 1.33/1.05    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/1.05    inference(flattening,[],[f26])).
% 1.33/1.05  
% 1.33/1.05  fof(f30,plain,(
% 1.33/1.05    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/1.05    inference(nnf_transformation,[],[f27])).
% 1.33/1.05  
% 1.33/1.05  fof(f31,plain,(
% 1.33/1.05    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/1.05    inference(flattening,[],[f30])).
% 1.33/1.05  
% 1.33/1.05  fof(f34,plain,(
% 1.33/1.05    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK3 & ! [X3] : (((r2_hidden(X3,sK3) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.33/1.05    introduced(choice_axiom,[])).
% 1.33/1.05  
% 1.33/1.05  fof(f33,plain,(
% 1.33/1.05    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK2,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.33/1.05    introduced(choice_axiom,[])).
% 1.33/1.05  
% 1.33/1.05  fof(f32,plain,(
% 1.33/1.05    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK1) & v3_pre_topc(X3,sK1)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.33/1.05    introduced(choice_axiom,[])).
% 1.33/1.05  
% 1.33/1.05  fof(f35,plain,(
% 1.33/1.05    ((k1_xboole_0 = sK3 & ! [X3] : (((r2_hidden(X3,sK3) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1)) & ((r2_hidden(sK2,X3) & v4_pre_topc(X3,sK1) & v3_pre_topc(X3,sK1)) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.33/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).
% 1.33/1.05  
% 1.33/1.05  fof(f54,plain,(
% 1.33/1.05    ( ! [X3] : (r2_hidden(sK2,X3) | ~r2_hidden(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.33/1.05    inference(cnf_transformation,[],[f35])).
% 1.33/1.05  
% 1.33/1.05  fof(f56,plain,(
% 1.33/1.05    k1_xboole_0 = sK3),
% 1.33/1.05    inference(cnf_transformation,[],[f35])).
% 1.33/1.05  
% 1.33/1.05  fof(f8,axiom,(
% 1.33/1.05    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f19,plain,(
% 1.33/1.05    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.33/1.05    inference(ennf_transformation,[],[f8])).
% 1.33/1.05  
% 1.33/1.05  fof(f43,plain,(
% 1.33/1.05    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.33/1.05    inference(cnf_transformation,[],[f19])).
% 1.33/1.05  
% 1.33/1.05  fof(f7,axiom,(
% 1.33/1.05    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f18,plain,(
% 1.33/1.05    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.33/1.05    inference(ennf_transformation,[],[f7])).
% 1.33/1.05  
% 1.33/1.05  fof(f42,plain,(
% 1.33/1.05    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.33/1.05    inference(cnf_transformation,[],[f18])).
% 1.33/1.05  
% 1.33/1.05  fof(f49,plain,(
% 1.33/1.05    l1_pre_topc(sK1)),
% 1.33/1.05    inference(cnf_transformation,[],[f35])).
% 1.33/1.05  
% 1.33/1.05  fof(f9,axiom,(
% 1.33/1.05    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f20,plain,(
% 1.33/1.05    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/1.05    inference(ennf_transformation,[],[f9])).
% 1.33/1.05  
% 1.33/1.05  fof(f21,plain,(
% 1.33/1.05    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.33/1.05    inference(flattening,[],[f20])).
% 1.33/1.05  
% 1.33/1.05  fof(f44,plain,(
% 1.33/1.05    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/1.05    inference(cnf_transformation,[],[f21])).
% 1.33/1.05  
% 1.33/1.05  fof(f47,plain,(
% 1.33/1.05    ~v2_struct_0(sK1)),
% 1.33/1.05    inference(cnf_transformation,[],[f35])).
% 1.33/1.05  
% 1.33/1.05  fof(f50,plain,(
% 1.33/1.05    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.33/1.05    inference(cnf_transformation,[],[f35])).
% 1.33/1.05  
% 1.33/1.05  fof(f5,axiom,(
% 1.33/1.05    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f15,plain,(
% 1.33/1.05    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.33/1.05    inference(ennf_transformation,[],[f5])).
% 1.33/1.05  
% 1.33/1.05  fof(f16,plain,(
% 1.33/1.05    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.33/1.05    inference(flattening,[],[f15])).
% 1.33/1.05  
% 1.33/1.05  fof(f40,plain,(
% 1.33/1.05    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.33/1.05    inference(cnf_transformation,[],[f16])).
% 1.33/1.05  
% 1.33/1.05  fof(f55,plain,(
% 1.33/1.05    ( ! [X3] : (r2_hidden(X3,sK3) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.33/1.05    inference(cnf_transformation,[],[f35])).
% 1.33/1.05  
% 1.33/1.05  fof(f10,axiom,(
% 1.33/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f22,plain,(
% 1.33/1.05    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/1.05    inference(ennf_transformation,[],[f10])).
% 1.33/1.05  
% 1.33/1.05  fof(f23,plain,(
% 1.33/1.05    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/1.05    inference(flattening,[],[f22])).
% 1.33/1.05  
% 1.33/1.05  fof(f45,plain,(
% 1.33/1.05    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.33/1.05    inference(cnf_transformation,[],[f23])).
% 1.33/1.05  
% 1.33/1.05  fof(f48,plain,(
% 1.33/1.05    v2_pre_topc(sK1)),
% 1.33/1.05    inference(cnf_transformation,[],[f35])).
% 1.33/1.05  
% 1.33/1.05  fof(f11,axiom,(
% 1.33/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f24,plain,(
% 1.33/1.05    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/1.05    inference(ennf_transformation,[],[f11])).
% 1.33/1.05  
% 1.33/1.05  fof(f25,plain,(
% 1.33/1.05    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/1.05    inference(flattening,[],[f24])).
% 1.33/1.05  
% 1.33/1.05  fof(f46,plain,(
% 1.33/1.05    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.33/1.05    inference(cnf_transformation,[],[f25])).
% 1.33/1.05  
% 1.33/1.05  fof(f6,axiom,(
% 1.33/1.05    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f17,plain,(
% 1.33/1.05    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.33/1.05    inference(ennf_transformation,[],[f6])).
% 1.33/1.05  
% 1.33/1.05  fof(f41,plain,(
% 1.33/1.05    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.33/1.05    inference(cnf_transformation,[],[f17])).
% 1.33/1.05  
% 1.33/1.05  fof(f1,axiom,(
% 1.33/1.05    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f14,plain,(
% 1.33/1.05    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.33/1.05    inference(ennf_transformation,[],[f1])).
% 1.33/1.05  
% 1.33/1.05  fof(f36,plain,(
% 1.33/1.05    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.33/1.05    inference(cnf_transformation,[],[f14])).
% 1.33/1.05  
% 1.33/1.05  fof(f2,axiom,(
% 1.33/1.05    ? [X0] : v1_xboole_0(X0)),
% 1.33/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.05  
% 1.33/1.05  fof(f28,plain,(
% 1.33/1.05    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK0)),
% 1.33/1.05    introduced(choice_axiom,[])).
% 1.33/1.05  
% 1.33/1.05  fof(f29,plain,(
% 1.33/1.05    v1_xboole_0(sK0)),
% 1.33/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f28])).
% 1.33/1.05  
% 1.33/1.05  fof(f37,plain,(
% 1.33/1.05    v1_xboole_0(sK0)),
% 1.33/1.05    inference(cnf_transformation,[],[f29])).
% 1.33/1.05  
% 1.33/1.05  cnf(c_3,plain,
% 1.33/1.05      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.33/1.05      inference(cnf_transformation,[],[f39]) ).
% 1.33/1.05  
% 1.33/1.05  cnf(c_1110,plain,
% 1.33/1.05      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.33/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.33/1.05  
% 1.33/1.05  cnf(c_2,plain,
% 1.33/1.05      ( k2_subset_1(X0) = X0 ),
% 1.33/1.05      inference(cnf_transformation,[],[f38]) ).
% 1.33/1.05  
% 1.33/1.05  cnf(c_1127,plain,
% 1.33/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.33/1.05      inference(light_normalisation,[status(thm)],[c_1110,c_2]) ).
% 1.33/1.05  
% 1.33/1.05  cnf(c_13,negated_conjecture,
% 1.33/1.05      ( ~ r2_hidden(X0,sK3)
% 1.33/1.05      | r2_hidden(sK2,X0)
% 1.33/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.33/1.05      inference(cnf_transformation,[],[f54]) ).
% 1.33/1.05  
% 1.33/1.05  cnf(c_1107,plain,
% 1.33/1.05      ( r2_hidden(X0,sK3) != iProver_top
% 1.33/1.05      | r2_hidden(sK2,X0) = iProver_top
% 1.33/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.33/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.33/1.05  
% 1.33/1.05  cnf(c_11,negated_conjecture,
% 1.33/1.05      ( k1_xboole_0 = sK3 ),
% 1.33/1.05      inference(cnf_transformation,[],[f56]) ).
% 1.33/1.05  
% 1.33/1.05  cnf(c_7,plain,
% 1.33/1.06      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.33/1.06      inference(cnf_transformation,[],[f43]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_6,plain,
% 1.33/1.06      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.33/1.06      inference(cnf_transformation,[],[f42]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_229,plain,
% 1.33/1.06      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.33/1.06      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_18,negated_conjecture,
% 1.33/1.06      ( l1_pre_topc(sK1) ),
% 1.33/1.06      inference(cnf_transformation,[],[f49]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_269,plain,
% 1.33/1.06      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.33/1.06      inference(resolution_lifted,[status(thm)],[c_229,c_18]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_270,plain,
% 1.33/1.06      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.33/1.06      inference(unflattening,[status(thm)],[c_269]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1149,plain,
% 1.33/1.06      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 1.33/1.06      | r2_hidden(sK2,X0) = iProver_top
% 1.33/1.06      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.33/1.06      inference(light_normalisation,[status(thm)],[c_1107,c_11,c_270]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1564,plain,
% 1.33/1.06      ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 1.33/1.06      | r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top ),
% 1.33/1.06      inference(superposition,[status(thm)],[c_1127,c_1149]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_8,plain,
% 1.33/1.06      ( v2_struct_0(X0)
% 1.33/1.06      | ~ l1_struct_0(X0)
% 1.33/1.06      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.33/1.06      inference(cnf_transformation,[],[f44]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_20,negated_conjecture,
% 1.33/1.06      ( ~ v2_struct_0(sK1) ),
% 1.33/1.06      inference(cnf_transformation,[],[f47]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_216,plain,
% 1.33/1.06      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 1.33/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_217,plain,
% 1.33/1.06      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.33/1.06      inference(unflattening,[status(thm)],[c_216]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_45,plain,
% 1.33/1.06      ( v2_struct_0(sK1)
% 1.33/1.06      | ~ l1_struct_0(sK1)
% 1.33/1.06      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.33/1.06      inference(instantiation,[status(thm)],[c_8]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_48,plain,
% 1.33/1.06      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 1.33/1.06      inference(instantiation,[status(thm)],[c_7]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_219,plain,
% 1.33/1.06      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.33/1.06      inference(global_propositional_subsumption,
% 1.33/1.06                [status(thm)],
% 1.33/1.06                [c_217,c_20,c_18,c_45,c_48]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1104,plain,
% 1.33/1.06      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 1.33/1.06      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1121,plain,
% 1.33/1.06      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 1.33/1.06      inference(light_normalisation,[status(thm)],[c_1104,c_270]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_17,negated_conjecture,
% 1.33/1.06      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.33/1.06      inference(cnf_transformation,[],[f50]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1105,plain,
% 1.33/1.06      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.33/1.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1124,plain,
% 1.33/1.06      ( m1_subset_1(sK2,k2_struct_0(sK1)) = iProver_top ),
% 1.33/1.06      inference(light_normalisation,[status(thm)],[c_1105,c_270]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_4,plain,
% 1.33/1.06      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.33/1.06      inference(cnf_transformation,[],[f40]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1109,plain,
% 1.33/1.06      ( r2_hidden(X0,X1) = iProver_top
% 1.33/1.06      | m1_subset_1(X0,X1) != iProver_top
% 1.33/1.06      | v1_xboole_0(X1) = iProver_top ),
% 1.33/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1646,plain,
% 1.33/1.06      ( r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top
% 1.33/1.06      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 1.33/1.06      inference(superposition,[status(thm)],[c_1124,c_1109]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1749,plain,
% 1.33/1.06      ( r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top ),
% 1.33/1.06      inference(global_propositional_subsumption,
% 1.33/1.06                [status(thm)],
% 1.33/1.06                [c_1564,c_1121,c_1646]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_12,negated_conjecture,
% 1.33/1.06      ( ~ v3_pre_topc(X0,sK1)
% 1.33/1.06      | ~ v4_pre_topc(X0,sK1)
% 1.33/1.06      | r2_hidden(X0,sK3)
% 1.33/1.06      | ~ r2_hidden(sK2,X0)
% 1.33/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.33/1.06      inference(cnf_transformation,[],[f55]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_9,plain,
% 1.33/1.06      ( v4_pre_topc(k2_struct_0(X0),X0)
% 1.33/1.06      | ~ v2_pre_topc(X0)
% 1.33/1.06      | ~ l1_pre_topc(X0) ),
% 1.33/1.06      inference(cnf_transformation,[],[f45]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_19,negated_conjecture,
% 1.33/1.06      ( v2_pre_topc(sK1) ),
% 1.33/1.06      inference(cnf_transformation,[],[f48]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_254,plain,
% 1.33/1.06      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK1 != X0 ),
% 1.33/1.06      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_255,plain,
% 1.33/1.06      ( v4_pre_topc(k2_struct_0(sK1),sK1) | ~ l1_pre_topc(sK1) ),
% 1.33/1.06      inference(unflattening,[status(thm)],[c_254]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_42,plain,
% 1.33/1.06      ( v4_pre_topc(k2_struct_0(sK1),sK1)
% 1.33/1.06      | ~ v2_pre_topc(sK1)
% 1.33/1.06      | ~ l1_pre_topc(sK1) ),
% 1.33/1.06      inference(instantiation,[status(thm)],[c_9]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_257,plain,
% 1.33/1.06      ( v4_pre_topc(k2_struct_0(sK1),sK1) ),
% 1.33/1.06      inference(global_propositional_subsumption,
% 1.33/1.06                [status(thm)],
% 1.33/1.06                [c_255,c_19,c_18,c_42]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_276,plain,
% 1.33/1.06      ( ~ v3_pre_topc(X0,sK1)
% 1.33/1.06      | r2_hidden(X0,sK3)
% 1.33/1.06      | ~ r2_hidden(sK2,X0)
% 1.33/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.33/1.06      | k2_struct_0(sK1) != X0
% 1.33/1.06      | sK1 != sK1 ),
% 1.33/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_257]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_277,plain,
% 1.33/1.06      ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
% 1.33/1.06      | r2_hidden(k2_struct_0(sK1),sK3)
% 1.33/1.06      | ~ r2_hidden(sK2,k2_struct_0(sK1))
% 1.33/1.06      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.33/1.06      inference(unflattening,[status(thm)],[c_276]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_10,plain,
% 1.33/1.06      ( v3_pre_topc(k2_struct_0(X0),X0)
% 1.33/1.06      | ~ v2_pre_topc(X0)
% 1.33/1.06      | ~ l1_pre_topc(X0) ),
% 1.33/1.06      inference(cnf_transformation,[],[f46]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_39,plain,
% 1.33/1.06      ( v3_pre_topc(k2_struct_0(sK1),sK1)
% 1.33/1.06      | ~ v2_pre_topc(sK1)
% 1.33/1.06      | ~ l1_pre_topc(sK1) ),
% 1.33/1.06      inference(instantiation,[status(thm)],[c_10]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_279,plain,
% 1.33/1.06      ( r2_hidden(k2_struct_0(sK1),sK3)
% 1.33/1.06      | ~ r2_hidden(sK2,k2_struct_0(sK1))
% 1.33/1.06      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.33/1.06      inference(global_propositional_subsumption,
% 1.33/1.06                [status(thm)],
% 1.33/1.06                [c_277,c_19,c_18,c_39]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1103,plain,
% 1.33/1.06      ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
% 1.33/1.06      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
% 1.33/1.06      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.33/1.06      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1156,plain,
% 1.33/1.06      ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
% 1.33/1.06      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
% 1.33/1.06      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.33/1.06      inference(light_normalisation,[status(thm)],[c_1103,c_11,c_270]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1160,plain,
% 1.33/1.06      ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
% 1.33/1.06      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
% 1.33/1.06      inference(forward_subsumption_resolution,
% 1.33/1.06                [status(thm)],
% 1.33/1.06                [c_1156,c_1127]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1754,plain,
% 1.33/1.06      ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
% 1.33/1.06      inference(superposition,[status(thm)],[c_1749,c_1160]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_5,plain,
% 1.33/1.06      ( ~ r2_hidden(X0,X1)
% 1.33/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.33/1.06      | ~ v1_xboole_0(X2) ),
% 1.33/1.06      inference(cnf_transformation,[],[f41]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1108,plain,
% 1.33/1.06      ( r2_hidden(X0,X1) != iProver_top
% 1.33/1.06      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 1.33/1.06      | v1_xboole_0(X2) != iProver_top ),
% 1.33/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1563,plain,
% 1.33/1.06      ( r2_hidden(X0,X1) != iProver_top
% 1.33/1.06      | v1_xboole_0(X1) != iProver_top ),
% 1.33/1.06      inference(superposition,[status(thm)],[c_1127,c_1108]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1914,plain,
% 1.33/1.06      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.33/1.06      inference(superposition,[status(thm)],[c_1754,c_1563]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_908,plain,
% 1.33/1.06      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.33/1.06      theory(equality) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1222,plain,
% 1.33/1.06      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK0) | X0 != sK0 ),
% 1.33/1.06      inference(instantiation,[status(thm)],[c_908]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1284,plain,
% 1.33/1.06      ( ~ v1_xboole_0(sK0)
% 1.33/1.06      | v1_xboole_0(k1_xboole_0)
% 1.33/1.06      | k1_xboole_0 != sK0 ),
% 1.33/1.06      inference(instantiation,[status(thm)],[c_1222]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1285,plain,
% 1.33/1.06      ( k1_xboole_0 != sK0
% 1.33/1.06      | v1_xboole_0(sK0) != iProver_top
% 1.33/1.06      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.33/1.06      inference(predicate_to_equality,[status(thm)],[c_1284]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_0,plain,
% 1.33/1.06      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.33/1.06      inference(cnf_transformation,[],[f36]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_1,plain,
% 1.33/1.06      ( v1_xboole_0(sK0) ),
% 1.33/1.06      inference(cnf_transformation,[],[f37]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_297,plain,
% 1.33/1.06      ( sK0 != X0 | k1_xboole_0 = X0 ),
% 1.33/1.06      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_298,plain,
% 1.33/1.06      ( k1_xboole_0 = sK0 ),
% 1.33/1.06      inference(unflattening,[status(thm)],[c_297]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(c_63,plain,
% 1.33/1.06      ( v1_xboole_0(sK0) = iProver_top ),
% 1.33/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.33/1.06  
% 1.33/1.06  cnf(contradiction,plain,
% 1.33/1.06      ( $false ),
% 1.33/1.06      inference(minisat,[status(thm)],[c_1914,c_1285,c_298,c_63]) ).
% 1.33/1.06  
% 1.33/1.06  
% 1.33/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.33/1.06  
% 1.33/1.06  ------                               Statistics
% 1.33/1.06  
% 1.33/1.06  ------ General
% 1.33/1.06  
% 1.33/1.06  abstr_ref_over_cycles:                  0
% 1.33/1.06  abstr_ref_under_cycles:                 0
% 1.33/1.06  gc_basic_clause_elim:                   0
% 1.33/1.06  forced_gc_time:                         0
% 1.33/1.06  parsing_time:                           0.012
% 1.33/1.06  unif_index_cands_time:                  0.
% 1.33/1.06  unif_index_add_time:                    0.
% 1.33/1.06  orderings_time:                         0.
% 1.33/1.06  out_proof_time:                         0.007
% 1.33/1.06  total_time:                             0.128
% 1.33/1.06  num_of_symbols:                         46
% 1.33/1.06  num_of_terms:                           1260
% 1.33/1.06  
% 1.33/1.06  ------ Preprocessing
% 1.33/1.06  
% 1.33/1.06  num_of_splits:                          0
% 1.33/1.06  num_of_split_atoms:                     0
% 1.33/1.06  num_of_reused_defs:                     0
% 1.33/1.06  num_eq_ax_congr_red:                    5
% 1.33/1.06  num_of_sem_filtered_clauses:            1
% 1.33/1.06  num_of_subtypes:                        0
% 1.33/1.06  monotx_restored_types:                  0
% 1.33/1.06  sat_num_of_epr_types:                   0
% 1.33/1.06  sat_num_of_non_cyclic_types:            0
% 1.33/1.06  sat_guarded_non_collapsed_types:        0
% 1.33/1.06  num_pure_diseq_elim:                    0
% 1.33/1.06  simp_replaced_by:                       0
% 1.33/1.06  res_preprocessed:                       77
% 1.33/1.06  prep_upred:                             0
% 1.33/1.06  prep_unflattend:                        39
% 1.33/1.06  smt_new_axioms:                         0
% 1.33/1.06  pred_elim_cands:                        3
% 1.33/1.06  pred_elim:                              6
% 1.33/1.06  pred_elim_cl:                           8
% 1.33/1.06  pred_elim_cycles:                       10
% 1.33/1.06  merged_defs:                            0
% 1.33/1.06  merged_defs_ncl:                        0
% 1.33/1.06  bin_hyper_res:                          0
% 1.33/1.06  prep_cycles:                            4
% 1.33/1.06  pred_elim_time:                         0.029
% 1.33/1.06  splitting_time:                         0.
% 1.33/1.06  sem_filter_time:                        0.
% 1.33/1.06  monotx_time:                            0.001
% 1.33/1.06  subtype_inf_time:                       0.
% 1.33/1.06  
% 1.33/1.06  ------ Problem properties
% 1.33/1.06  
% 1.33/1.06  clauses:                                13
% 1.33/1.06  conjectures:                            4
% 1.33/1.06  epr:                                    4
% 1.33/1.06  horn:                                   12
% 1.33/1.06  ground:                                 7
% 1.33/1.06  unary:                                  8
% 1.33/1.06  binary:                                 1
% 1.33/1.06  lits:                                   22
% 1.33/1.06  lits_eq:                                4
% 1.33/1.06  fd_pure:                                0
% 1.33/1.06  fd_pseudo:                              0
% 1.33/1.06  fd_cond:                                1
% 1.33/1.06  fd_pseudo_cond:                         0
% 1.33/1.06  ac_symbols:                             0
% 1.33/1.06  
% 1.33/1.06  ------ Propositional Solver
% 1.33/1.06  
% 1.33/1.06  prop_solver_calls:                      25
% 1.33/1.06  prop_fast_solver_calls:                 458
% 1.33/1.06  smt_solver_calls:                       0
% 1.33/1.06  smt_fast_solver_calls:                  0
% 1.33/1.06  prop_num_of_clauses:                    551
% 1.33/1.06  prop_preprocess_simplified:             2334
% 1.33/1.06  prop_fo_subsumed:                       7
% 1.33/1.06  prop_solver_time:                       0.
% 1.33/1.06  smt_solver_time:                        0.
% 1.33/1.06  smt_fast_solver_time:                   0.
% 1.33/1.06  prop_fast_solver_time:                  0.
% 1.33/1.06  prop_unsat_core_time:                   0.
% 1.33/1.06  
% 1.33/1.06  ------ QBF
% 1.33/1.06  
% 1.33/1.06  qbf_q_res:                              0
% 1.33/1.06  qbf_num_tautologies:                    0
% 1.33/1.06  qbf_prep_cycles:                        0
% 1.33/1.06  
% 1.33/1.06  ------ BMC1
% 1.33/1.06  
% 1.33/1.06  bmc1_current_bound:                     -1
% 1.33/1.06  bmc1_last_solved_bound:                 -1
% 1.33/1.06  bmc1_unsat_core_size:                   -1
% 1.33/1.06  bmc1_unsat_core_parents_size:           -1
% 1.33/1.06  bmc1_merge_next_fun:                    0
% 1.33/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.33/1.06  
% 1.33/1.06  ------ Instantiation
% 1.33/1.06  
% 1.33/1.06  inst_num_of_clauses:                    166
% 1.33/1.06  inst_num_in_passive:                    2
% 1.33/1.06  inst_num_in_active:                     96
% 1.33/1.06  inst_num_in_unprocessed:                68
% 1.33/1.06  inst_num_of_loops:                      100
% 1.33/1.06  inst_num_of_learning_restarts:          0
% 1.33/1.06  inst_num_moves_active_passive:          2
% 1.33/1.06  inst_lit_activity:                      0
% 1.33/1.06  inst_lit_activity_moves:                0
% 1.33/1.06  inst_num_tautologies:                   0
% 1.33/1.06  inst_num_prop_implied:                  0
% 1.33/1.06  inst_num_existing_simplified:           0
% 1.33/1.06  inst_num_eq_res_simplified:             0
% 1.33/1.06  inst_num_child_elim:                    0
% 1.33/1.06  inst_num_of_dismatching_blockings:      13
% 1.33/1.06  inst_num_of_non_proper_insts:           110
% 1.33/1.06  inst_num_of_duplicates:                 0
% 1.33/1.06  inst_inst_num_from_inst_to_res:         0
% 1.33/1.06  inst_dismatching_checking_time:         0.
% 1.33/1.06  
% 1.33/1.06  ------ Resolution
% 1.33/1.06  
% 1.33/1.06  res_num_of_clauses:                     0
% 1.33/1.06  res_num_in_passive:                     0
% 1.33/1.06  res_num_in_active:                      0
% 1.33/1.06  res_num_of_loops:                       81
% 1.33/1.06  res_forward_subset_subsumed:            7
% 1.33/1.06  res_backward_subset_subsumed:           0
% 1.33/1.06  res_forward_subsumed:                   0
% 1.33/1.06  res_backward_subsumed:                  0
% 1.33/1.06  res_forward_subsumption_resolution:     0
% 1.33/1.06  res_backward_subsumption_resolution:    0
% 1.33/1.06  res_clause_to_clause_subsumption:       36
% 1.33/1.06  res_orphan_elimination:                 0
% 1.33/1.06  res_tautology_del:                      23
% 1.33/1.06  res_num_eq_res_simplified:              0
% 1.33/1.06  res_num_sel_changes:                    0
% 1.33/1.06  res_moves_from_active_to_pass:          0
% 1.33/1.06  
% 1.33/1.06  ------ Superposition
% 1.33/1.06  
% 1.33/1.06  sup_time_total:                         0.
% 1.33/1.06  sup_time_generating:                    0.
% 1.33/1.06  sup_time_sim_full:                      0.
% 1.33/1.06  sup_time_sim_immed:                     0.
% 1.33/1.06  
% 1.33/1.06  sup_num_of_clauses:                     21
% 1.33/1.06  sup_num_in_active:                      18
% 1.33/1.06  sup_num_in_passive:                     3
% 1.33/1.06  sup_num_of_loops:                       19
% 1.33/1.06  sup_fw_superposition:                   8
% 1.33/1.06  sup_bw_superposition:                   4
% 1.33/1.06  sup_immediate_simplified:               0
% 1.33/1.06  sup_given_eliminated:                   0
% 1.33/1.06  comparisons_done:                       0
% 1.33/1.06  comparisons_avoided:                    0
% 1.33/1.06  
% 1.33/1.06  ------ Simplifications
% 1.33/1.06  
% 1.33/1.06  
% 1.33/1.06  sim_fw_subset_subsumed:                 0
% 1.33/1.06  sim_bw_subset_subsumed:                 2
% 1.33/1.06  sim_fw_subsumed:                        0
% 1.33/1.06  sim_bw_subsumed:                        0
% 1.33/1.06  sim_fw_subsumption_res:                 1
% 1.33/1.06  sim_bw_subsumption_res:                 0
% 1.33/1.06  sim_tautology_del:                      1
% 1.33/1.06  sim_eq_tautology_del:                   1
% 1.33/1.06  sim_eq_res_simp:                        0
% 1.33/1.06  sim_fw_demodulated:                     0
% 1.33/1.06  sim_bw_demodulated:                     1
% 1.33/1.06  sim_light_normalised:                   6
% 1.33/1.06  sim_joinable_taut:                      0
% 1.33/1.06  sim_joinable_simp:                      0
% 1.33/1.06  sim_ac_normalised:                      0
% 1.33/1.06  sim_smt_subsumption:                    0
% 1.33/1.06  
%------------------------------------------------------------------------------
