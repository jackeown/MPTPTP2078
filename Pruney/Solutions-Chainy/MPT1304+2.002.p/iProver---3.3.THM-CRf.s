%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:26 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 374 expanded)
%              Number of clauses        :   53 (  98 expanded)
%              Number of leaves         :   23 (  99 expanded)
%              Depth                    :   17
%              Number of atoms          :  350 (1228 expanded)
%              Number of equality atoms :  101 ( 234 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK3),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK2,X2),X0)
            & v1_tops_2(sK2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X1,X2),sK1)
              & v1_tops_2(X1,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1)
    & v1_tops_2(sK2,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42,f41,f40])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f75])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f76])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f78])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f71,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1056,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1061,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2333,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0) ),
    inference(superposition,[status(thm)],[c_1056,c_1061])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1067,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2926,plain,
    ( r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),X1) = iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)),X1) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_1067])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1068,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4354,plain,
    ( r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),X1) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2926,c_1068])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1063,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1060,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1668,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1060])).

cnf(c_14,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_276,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_277,plain,
    ( ~ v1_tops_2(X0,sK1)
    | v1_tops_2(X1,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_1055,plain,
    ( v1_tops_2(X0,sK1) != iProver_top
    | v1_tops_2(X1,sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_2015,plain,
    ( v1_tops_2(X0,sK1) != iProver_top
    | v1_tops_2(X1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1055])).

cnf(c_2208,plain,
    ( v1_tops_2(X0,sK1) = iProver_top
    | v1_tops_2(sK2,sK1) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_2015])).

cnf(c_16,negated_conjecture,
    ( v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_459,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_460,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_459])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_262,c_460])).

cnf(c_1054,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_1521,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1054])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1636,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2))
    | r1_tarski(X0,k1_zfmisc_1(X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2872,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_2873,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2872])).

cnf(c_3001,plain,
    ( v1_tops_2(X0,sK1) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2208,c_23,c_1521,c_2873])).

cnf(c_4360,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),sK1) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4354,c_3001])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1420,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1423,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1420])).

cnf(c_1426,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2380,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)),sK2)
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_2381,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)),sK2) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2380])).

cnf(c_3011,plain,
    ( v1_tops_2(k5_xboole_0(X0,X1),sK1) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_3001])).

cnf(c_3377,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),sK1) = iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)),sK2) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_3011])).

cnf(c_4397,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4360,c_1423,c_2381,c_3377])).

cnf(c_15,negated_conjecture,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1059,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4404,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4397,c_1059])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.51/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/0.98  
% 2.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.51/0.98  
% 2.51/0.98  ------  iProver source info
% 2.51/0.98  
% 2.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.51/0.98  git: non_committed_changes: false
% 2.51/0.98  git: last_make_outside_of_git: false
% 2.51/0.98  
% 2.51/0.98  ------ 
% 2.51/0.98  
% 2.51/0.98  ------ Input Options
% 2.51/0.98  
% 2.51/0.98  --out_options                           all
% 2.51/0.98  --tptp_safe_out                         true
% 2.51/0.98  --problem_path                          ""
% 2.51/0.98  --include_path                          ""
% 2.51/0.98  --clausifier                            res/vclausify_rel
% 2.51/0.98  --clausifier_options                    --mode clausify
% 2.51/0.98  --stdin                                 false
% 2.51/0.98  --stats_out                             all
% 2.51/0.98  
% 2.51/0.98  ------ General Options
% 2.51/0.98  
% 2.51/0.98  --fof                                   false
% 2.51/0.98  --time_out_real                         305.
% 2.51/0.98  --time_out_virtual                      -1.
% 2.51/0.98  --symbol_type_check                     false
% 2.51/0.98  --clausify_out                          false
% 2.51/0.98  --sig_cnt_out                           false
% 2.51/0.98  --trig_cnt_out                          false
% 2.51/0.98  --trig_cnt_out_tolerance                1.
% 2.51/0.98  --trig_cnt_out_sk_spl                   false
% 2.51/0.98  --abstr_cl_out                          false
% 2.51/0.98  
% 2.51/0.98  ------ Global Options
% 2.51/0.98  
% 2.51/0.98  --schedule                              default
% 2.51/0.98  --add_important_lit                     false
% 2.51/0.98  --prop_solver_per_cl                    1000
% 2.51/0.98  --min_unsat_core                        false
% 2.51/0.98  --soft_assumptions                      false
% 2.51/0.98  --soft_lemma_size                       3
% 2.51/0.98  --prop_impl_unit_size                   0
% 2.51/0.98  --prop_impl_unit                        []
% 2.51/0.98  --share_sel_clauses                     true
% 2.51/0.98  --reset_solvers                         false
% 2.51/0.98  --bc_imp_inh                            [conj_cone]
% 2.51/0.98  --conj_cone_tolerance                   3.
% 2.51/0.98  --extra_neg_conj                        none
% 2.51/0.98  --large_theory_mode                     true
% 2.51/0.98  --prolific_symb_bound                   200
% 2.51/0.98  --lt_threshold                          2000
% 2.51/0.98  --clause_weak_htbl                      true
% 2.51/0.98  --gc_record_bc_elim                     false
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing Options
% 2.51/0.98  
% 2.51/0.98  --preprocessing_flag                    true
% 2.51/0.98  --time_out_prep_mult                    0.1
% 2.51/0.98  --splitting_mode                        input
% 2.51/0.98  --splitting_grd                         true
% 2.51/0.98  --splitting_cvd                         false
% 2.51/0.98  --splitting_cvd_svl                     false
% 2.51/0.98  --splitting_nvd                         32
% 2.51/0.98  --sub_typing                            true
% 2.51/0.98  --prep_gs_sim                           true
% 2.51/0.98  --prep_unflatten                        true
% 2.51/0.98  --prep_res_sim                          true
% 2.51/0.98  --prep_upred                            true
% 2.51/0.98  --prep_sem_filter                       exhaustive
% 2.51/0.98  --prep_sem_filter_out                   false
% 2.51/0.98  --pred_elim                             true
% 2.51/0.98  --res_sim_input                         true
% 2.51/0.98  --eq_ax_congr_red                       true
% 2.51/0.98  --pure_diseq_elim                       true
% 2.51/0.98  --brand_transform                       false
% 2.51/0.98  --non_eq_to_eq                          false
% 2.51/0.98  --prep_def_merge                        true
% 2.51/0.98  --prep_def_merge_prop_impl              false
% 2.51/0.98  --prep_def_merge_mbd                    true
% 2.51/0.98  --prep_def_merge_tr_red                 false
% 2.51/0.98  --prep_def_merge_tr_cl                  false
% 2.51/0.98  --smt_preprocessing                     true
% 2.51/0.98  --smt_ac_axioms                         fast
% 2.51/0.98  --preprocessed_out                      false
% 2.51/0.98  --preprocessed_stats                    false
% 2.51/0.98  
% 2.51/0.98  ------ Abstraction refinement Options
% 2.51/0.98  
% 2.51/0.98  --abstr_ref                             []
% 2.51/0.98  --abstr_ref_prep                        false
% 2.51/0.98  --abstr_ref_until_sat                   false
% 2.51/0.98  --abstr_ref_sig_restrict                funpre
% 2.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/0.98  --abstr_ref_under                       []
% 2.51/0.98  
% 2.51/0.98  ------ SAT Options
% 2.51/0.98  
% 2.51/0.98  --sat_mode                              false
% 2.51/0.98  --sat_fm_restart_options                ""
% 2.51/0.98  --sat_gr_def                            false
% 2.51/0.98  --sat_epr_types                         true
% 2.51/0.98  --sat_non_cyclic_types                  false
% 2.51/0.98  --sat_finite_models                     false
% 2.51/0.98  --sat_fm_lemmas                         false
% 2.51/0.98  --sat_fm_prep                           false
% 2.51/0.98  --sat_fm_uc_incr                        true
% 2.51/0.98  --sat_out_model                         small
% 2.51/0.98  --sat_out_clauses                       false
% 2.51/0.98  
% 2.51/0.98  ------ QBF Options
% 2.51/0.98  
% 2.51/0.98  --qbf_mode                              false
% 2.51/0.98  --qbf_elim_univ                         false
% 2.51/0.98  --qbf_dom_inst                          none
% 2.51/0.98  --qbf_dom_pre_inst                      false
% 2.51/0.98  --qbf_sk_in                             false
% 2.51/0.98  --qbf_pred_elim                         true
% 2.51/0.98  --qbf_split                             512
% 2.51/0.98  
% 2.51/0.98  ------ BMC1 Options
% 2.51/0.98  
% 2.51/0.98  --bmc1_incremental                      false
% 2.51/0.98  --bmc1_axioms                           reachable_all
% 2.51/0.98  --bmc1_min_bound                        0
% 2.51/0.98  --bmc1_max_bound                        -1
% 2.51/0.98  --bmc1_max_bound_default                -1
% 2.51/0.98  --bmc1_symbol_reachability              true
% 2.51/0.98  --bmc1_property_lemmas                  false
% 2.51/0.98  --bmc1_k_induction                      false
% 2.51/0.98  --bmc1_non_equiv_states                 false
% 2.51/0.98  --bmc1_deadlock                         false
% 2.51/0.98  --bmc1_ucm                              false
% 2.51/0.98  --bmc1_add_unsat_core                   none
% 2.51/0.98  --bmc1_unsat_core_children              false
% 2.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/0.98  --bmc1_out_stat                         full
% 2.51/0.98  --bmc1_ground_init                      false
% 2.51/0.98  --bmc1_pre_inst_next_state              false
% 2.51/0.98  --bmc1_pre_inst_state                   false
% 2.51/0.98  --bmc1_pre_inst_reach_state             false
% 2.51/0.98  --bmc1_out_unsat_core                   false
% 2.51/0.98  --bmc1_aig_witness_out                  false
% 2.51/0.98  --bmc1_verbose                          false
% 2.51/0.98  --bmc1_dump_clauses_tptp                false
% 2.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.51/0.98  --bmc1_dump_file                        -
% 2.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.51/0.98  --bmc1_ucm_extend_mode                  1
% 2.51/0.98  --bmc1_ucm_init_mode                    2
% 2.51/0.98  --bmc1_ucm_cone_mode                    none
% 2.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.51/0.98  --bmc1_ucm_relax_model                  4
% 2.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/0.98  --bmc1_ucm_layered_model                none
% 2.51/0.98  --bmc1_ucm_max_lemma_size               10
% 2.51/0.98  
% 2.51/0.98  ------ AIG Options
% 2.51/0.98  
% 2.51/0.98  --aig_mode                              false
% 2.51/0.98  
% 2.51/0.98  ------ Instantiation Options
% 2.51/0.98  
% 2.51/0.98  --instantiation_flag                    true
% 2.51/0.98  --inst_sos_flag                         false
% 2.51/0.98  --inst_sos_phase                        true
% 2.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/0.98  --inst_lit_sel_side                     num_symb
% 2.51/0.98  --inst_solver_per_active                1400
% 2.51/0.98  --inst_solver_calls_frac                1.
% 2.51/0.98  --inst_passive_queue_type               priority_queues
% 2.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/0.98  --inst_passive_queues_freq              [25;2]
% 2.51/0.98  --inst_dismatching                      true
% 2.51/0.98  --inst_eager_unprocessed_to_passive     true
% 2.51/0.98  --inst_prop_sim_given                   true
% 2.51/0.98  --inst_prop_sim_new                     false
% 2.51/0.98  --inst_subs_new                         false
% 2.51/0.98  --inst_eq_res_simp                      false
% 2.51/0.98  --inst_subs_given                       false
% 2.51/0.98  --inst_orphan_elimination               true
% 2.51/0.98  --inst_learning_loop_flag               true
% 2.51/0.98  --inst_learning_start                   3000
% 2.51/0.98  --inst_learning_factor                  2
% 2.51/0.98  --inst_start_prop_sim_after_learn       3
% 2.51/0.98  --inst_sel_renew                        solver
% 2.51/0.98  --inst_lit_activity_flag                true
% 2.51/0.98  --inst_restr_to_given                   false
% 2.51/0.98  --inst_activity_threshold               500
% 2.51/0.98  --inst_out_proof                        true
% 2.51/0.98  
% 2.51/0.98  ------ Resolution Options
% 2.51/0.98  
% 2.51/0.98  --resolution_flag                       true
% 2.51/0.98  --res_lit_sel                           adaptive
% 2.51/0.98  --res_lit_sel_side                      none
% 2.51/0.98  --res_ordering                          kbo
% 2.51/0.98  --res_to_prop_solver                    active
% 2.51/0.98  --res_prop_simpl_new                    false
% 2.51/0.98  --res_prop_simpl_given                  true
% 2.51/0.98  --res_passive_queue_type                priority_queues
% 2.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/0.98  --res_passive_queues_freq               [15;5]
% 2.51/0.98  --res_forward_subs                      full
% 2.51/0.98  --res_backward_subs                     full
% 2.51/0.98  --res_forward_subs_resolution           true
% 2.51/0.98  --res_backward_subs_resolution          true
% 2.51/0.98  --res_orphan_elimination                true
% 2.51/0.98  --res_time_limit                        2.
% 2.51/0.98  --res_out_proof                         true
% 2.51/0.98  
% 2.51/0.98  ------ Superposition Options
% 2.51/0.98  
% 2.51/0.98  --superposition_flag                    true
% 2.51/0.98  --sup_passive_queue_type                priority_queues
% 2.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.51/0.98  --demod_completeness_check              fast
% 2.51/0.98  --demod_use_ground                      true
% 2.51/0.98  --sup_to_prop_solver                    passive
% 2.51/0.98  --sup_prop_simpl_new                    true
% 2.51/0.98  --sup_prop_simpl_given                  true
% 2.51/0.98  --sup_fun_splitting                     false
% 2.51/0.98  --sup_smt_interval                      50000
% 2.51/0.98  
% 2.51/0.98  ------ Superposition Simplification Setup
% 2.51/0.98  
% 2.51/0.98  --sup_indices_passive                   []
% 2.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_full_bw                           [BwDemod]
% 2.51/0.98  --sup_immed_triv                        [TrivRules]
% 2.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_immed_bw_main                     []
% 2.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.98  
% 2.51/0.98  ------ Combination Options
% 2.51/0.98  
% 2.51/0.98  --comb_res_mult                         3
% 2.51/0.98  --comb_sup_mult                         2
% 2.51/0.98  --comb_inst_mult                        10
% 2.51/0.98  
% 2.51/0.98  ------ Debug Options
% 2.51/0.98  
% 2.51/0.98  --dbg_backtrace                         false
% 2.51/0.98  --dbg_dump_prop_clauses                 false
% 2.51/0.98  --dbg_dump_prop_clauses_file            -
% 2.51/0.98  --dbg_out_stat                          false
% 2.51/0.98  ------ Parsing...
% 2.51/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.51/0.98  ------ Proving...
% 2.51/0.98  ------ Problem Properties 
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  clauses                                 17
% 2.51/0.98  conjectures                             4
% 2.51/0.98  EPR                                     5
% 2.51/0.98  Horn                                    16
% 2.51/0.98  unary                                   5
% 2.51/0.98  binary                                  6
% 2.51/0.98  lits                                    37
% 2.51/0.98  lits eq                                 4
% 2.51/0.98  fd_pure                                 0
% 2.51/0.98  fd_pseudo                               0
% 2.51/0.98  fd_cond                                 0
% 2.51/0.98  fd_pseudo_cond                          3
% 2.51/0.98  AC symbols                              0
% 2.51/0.98  
% 2.51/0.98  ------ Schedule dynamic 5 is on 
% 2.51/0.98  
% 2.51/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  ------ 
% 2.51/0.98  Current options:
% 2.51/0.98  ------ 
% 2.51/0.98  
% 2.51/0.98  ------ Input Options
% 2.51/0.98  
% 2.51/0.98  --out_options                           all
% 2.51/0.98  --tptp_safe_out                         true
% 2.51/0.98  --problem_path                          ""
% 2.51/0.98  --include_path                          ""
% 2.51/0.98  --clausifier                            res/vclausify_rel
% 2.51/0.98  --clausifier_options                    --mode clausify
% 2.51/0.98  --stdin                                 false
% 2.51/0.98  --stats_out                             all
% 2.51/0.98  
% 2.51/0.98  ------ General Options
% 2.51/0.98  
% 2.51/0.98  --fof                                   false
% 2.51/0.98  --time_out_real                         305.
% 2.51/0.98  --time_out_virtual                      -1.
% 2.51/0.98  --symbol_type_check                     false
% 2.51/0.98  --clausify_out                          false
% 2.51/0.98  --sig_cnt_out                           false
% 2.51/0.98  --trig_cnt_out                          false
% 2.51/0.98  --trig_cnt_out_tolerance                1.
% 2.51/0.98  --trig_cnt_out_sk_spl                   false
% 2.51/0.98  --abstr_cl_out                          false
% 2.51/0.98  
% 2.51/0.98  ------ Global Options
% 2.51/0.98  
% 2.51/0.98  --schedule                              default
% 2.51/0.98  --add_important_lit                     false
% 2.51/0.98  --prop_solver_per_cl                    1000
% 2.51/0.98  --min_unsat_core                        false
% 2.51/0.98  --soft_assumptions                      false
% 2.51/0.98  --soft_lemma_size                       3
% 2.51/0.98  --prop_impl_unit_size                   0
% 2.51/0.98  --prop_impl_unit                        []
% 2.51/0.98  --share_sel_clauses                     true
% 2.51/0.98  --reset_solvers                         false
% 2.51/0.98  --bc_imp_inh                            [conj_cone]
% 2.51/0.98  --conj_cone_tolerance                   3.
% 2.51/0.98  --extra_neg_conj                        none
% 2.51/0.98  --large_theory_mode                     true
% 2.51/0.98  --prolific_symb_bound                   200
% 2.51/0.98  --lt_threshold                          2000
% 2.51/0.98  --clause_weak_htbl                      true
% 2.51/0.98  --gc_record_bc_elim                     false
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing Options
% 2.51/0.98  
% 2.51/0.98  --preprocessing_flag                    true
% 2.51/0.98  --time_out_prep_mult                    0.1
% 2.51/0.98  --splitting_mode                        input
% 2.51/0.98  --splitting_grd                         true
% 2.51/0.98  --splitting_cvd                         false
% 2.51/0.98  --splitting_cvd_svl                     false
% 2.51/0.98  --splitting_nvd                         32
% 2.51/0.98  --sub_typing                            true
% 2.51/0.98  --prep_gs_sim                           true
% 2.51/0.98  --prep_unflatten                        true
% 2.51/0.98  --prep_res_sim                          true
% 2.51/0.98  --prep_upred                            true
% 2.51/0.98  --prep_sem_filter                       exhaustive
% 2.51/0.98  --prep_sem_filter_out                   false
% 2.51/0.98  --pred_elim                             true
% 2.51/0.98  --res_sim_input                         true
% 2.51/0.98  --eq_ax_congr_red                       true
% 2.51/0.98  --pure_diseq_elim                       true
% 2.51/0.98  --brand_transform                       false
% 2.51/0.98  --non_eq_to_eq                          false
% 2.51/0.98  --prep_def_merge                        true
% 2.51/0.98  --prep_def_merge_prop_impl              false
% 2.51/0.98  --prep_def_merge_mbd                    true
% 2.51/0.98  --prep_def_merge_tr_red                 false
% 2.51/0.98  --prep_def_merge_tr_cl                  false
% 2.51/0.98  --smt_preprocessing                     true
% 2.51/0.98  --smt_ac_axioms                         fast
% 2.51/0.98  --preprocessed_out                      false
% 2.51/0.98  --preprocessed_stats                    false
% 2.51/0.98  
% 2.51/0.98  ------ Abstraction refinement Options
% 2.51/0.98  
% 2.51/0.98  --abstr_ref                             []
% 2.51/0.98  --abstr_ref_prep                        false
% 2.51/0.98  --abstr_ref_until_sat                   false
% 2.51/0.98  --abstr_ref_sig_restrict                funpre
% 2.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/0.98  --abstr_ref_under                       []
% 2.51/0.98  
% 2.51/0.98  ------ SAT Options
% 2.51/0.98  
% 2.51/0.98  --sat_mode                              false
% 2.51/0.98  --sat_fm_restart_options                ""
% 2.51/0.98  --sat_gr_def                            false
% 2.51/0.98  --sat_epr_types                         true
% 2.51/0.98  --sat_non_cyclic_types                  false
% 2.51/0.98  --sat_finite_models                     false
% 2.51/0.98  --sat_fm_lemmas                         false
% 2.51/0.98  --sat_fm_prep                           false
% 2.51/0.98  --sat_fm_uc_incr                        true
% 2.51/0.98  --sat_out_model                         small
% 2.51/0.98  --sat_out_clauses                       false
% 2.51/0.98  
% 2.51/0.98  ------ QBF Options
% 2.51/0.98  
% 2.51/0.98  --qbf_mode                              false
% 2.51/0.98  --qbf_elim_univ                         false
% 2.51/0.98  --qbf_dom_inst                          none
% 2.51/0.98  --qbf_dom_pre_inst                      false
% 2.51/0.98  --qbf_sk_in                             false
% 2.51/0.98  --qbf_pred_elim                         true
% 2.51/0.98  --qbf_split                             512
% 2.51/0.98  
% 2.51/0.98  ------ BMC1 Options
% 2.51/0.98  
% 2.51/0.98  --bmc1_incremental                      false
% 2.51/0.98  --bmc1_axioms                           reachable_all
% 2.51/0.98  --bmc1_min_bound                        0
% 2.51/0.98  --bmc1_max_bound                        -1
% 2.51/0.98  --bmc1_max_bound_default                -1
% 2.51/0.98  --bmc1_symbol_reachability              true
% 2.51/0.98  --bmc1_property_lemmas                  false
% 2.51/0.98  --bmc1_k_induction                      false
% 2.51/0.98  --bmc1_non_equiv_states                 false
% 2.51/0.98  --bmc1_deadlock                         false
% 2.51/0.98  --bmc1_ucm                              false
% 2.51/0.98  --bmc1_add_unsat_core                   none
% 2.51/0.98  --bmc1_unsat_core_children              false
% 2.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/0.98  --bmc1_out_stat                         full
% 2.51/0.98  --bmc1_ground_init                      false
% 2.51/0.98  --bmc1_pre_inst_next_state              false
% 2.51/0.98  --bmc1_pre_inst_state                   false
% 2.51/0.98  --bmc1_pre_inst_reach_state             false
% 2.51/0.98  --bmc1_out_unsat_core                   false
% 2.51/0.98  --bmc1_aig_witness_out                  false
% 2.51/0.98  --bmc1_verbose                          false
% 2.51/0.98  --bmc1_dump_clauses_tptp                false
% 2.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.51/0.98  --bmc1_dump_file                        -
% 2.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.51/0.98  --bmc1_ucm_extend_mode                  1
% 2.51/0.98  --bmc1_ucm_init_mode                    2
% 2.51/0.98  --bmc1_ucm_cone_mode                    none
% 2.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.51/0.98  --bmc1_ucm_relax_model                  4
% 2.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/0.98  --bmc1_ucm_layered_model                none
% 2.51/0.98  --bmc1_ucm_max_lemma_size               10
% 2.51/0.98  
% 2.51/0.98  ------ AIG Options
% 2.51/0.98  
% 2.51/0.98  --aig_mode                              false
% 2.51/0.98  
% 2.51/0.98  ------ Instantiation Options
% 2.51/0.98  
% 2.51/0.98  --instantiation_flag                    true
% 2.51/0.98  --inst_sos_flag                         false
% 2.51/0.98  --inst_sos_phase                        true
% 2.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/0.98  --inst_lit_sel_side                     none
% 2.51/0.98  --inst_solver_per_active                1400
% 2.51/0.98  --inst_solver_calls_frac                1.
% 2.51/0.98  --inst_passive_queue_type               priority_queues
% 2.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/0.98  --inst_passive_queues_freq              [25;2]
% 2.51/0.98  --inst_dismatching                      true
% 2.51/0.98  --inst_eager_unprocessed_to_passive     true
% 2.51/0.98  --inst_prop_sim_given                   true
% 2.51/0.98  --inst_prop_sim_new                     false
% 2.51/0.98  --inst_subs_new                         false
% 2.51/0.98  --inst_eq_res_simp                      false
% 2.51/0.98  --inst_subs_given                       false
% 2.51/0.98  --inst_orphan_elimination               true
% 2.51/0.98  --inst_learning_loop_flag               true
% 2.51/0.98  --inst_learning_start                   3000
% 2.51/0.98  --inst_learning_factor                  2
% 2.51/0.98  --inst_start_prop_sim_after_learn       3
% 2.51/0.98  --inst_sel_renew                        solver
% 2.51/0.98  --inst_lit_activity_flag                true
% 2.51/0.98  --inst_restr_to_given                   false
% 2.51/0.98  --inst_activity_threshold               500
% 2.51/0.98  --inst_out_proof                        true
% 2.51/0.98  
% 2.51/0.98  ------ Resolution Options
% 2.51/0.98  
% 2.51/0.98  --resolution_flag                       false
% 2.51/0.98  --res_lit_sel                           adaptive
% 2.51/0.98  --res_lit_sel_side                      none
% 2.51/0.98  --res_ordering                          kbo
% 2.51/0.98  --res_to_prop_solver                    active
% 2.51/0.98  --res_prop_simpl_new                    false
% 2.51/0.98  --res_prop_simpl_given                  true
% 2.51/0.98  --res_passive_queue_type                priority_queues
% 2.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/0.98  --res_passive_queues_freq               [15;5]
% 2.51/0.98  --res_forward_subs                      full
% 2.51/0.98  --res_backward_subs                     full
% 2.51/0.98  --res_forward_subs_resolution           true
% 2.51/0.98  --res_backward_subs_resolution          true
% 2.51/0.98  --res_orphan_elimination                true
% 2.51/0.98  --res_time_limit                        2.
% 2.51/0.98  --res_out_proof                         true
% 2.51/0.98  
% 2.51/0.98  ------ Superposition Options
% 2.51/0.98  
% 2.51/0.98  --superposition_flag                    true
% 2.51/0.98  --sup_passive_queue_type                priority_queues
% 2.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.51/0.98  --demod_completeness_check              fast
% 2.51/0.98  --demod_use_ground                      true
% 2.51/0.98  --sup_to_prop_solver                    passive
% 2.51/0.98  --sup_prop_simpl_new                    true
% 2.51/0.98  --sup_prop_simpl_given                  true
% 2.51/0.98  --sup_fun_splitting                     false
% 2.51/0.98  --sup_smt_interval                      50000
% 2.51/0.98  
% 2.51/0.98  ------ Superposition Simplification Setup
% 2.51/0.98  
% 2.51/0.98  --sup_indices_passive                   []
% 2.51/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_full_bw                           [BwDemod]
% 2.51/0.98  --sup_immed_triv                        [TrivRules]
% 2.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_immed_bw_main                     []
% 2.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.98  
% 2.51/0.98  ------ Combination Options
% 2.51/0.98  
% 2.51/0.98  --comb_res_mult                         3
% 2.51/0.98  --comb_sup_mult                         2
% 2.51/0.98  --comb_inst_mult                        10
% 2.51/0.98  
% 2.51/0.98  ------ Debug Options
% 2.51/0.98  
% 2.51/0.98  --dbg_backtrace                         false
% 2.51/0.98  --dbg_dump_prop_clauses                 false
% 2.51/0.98  --dbg_dump_prop_clauses_file            -
% 2.51/0.98  --dbg_out_stat                          false
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  ------ Proving...
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  % SZS status Theorem for theBenchmark.p
% 2.51/0.98  
% 2.51/0.98   Resolution empty clause
% 2.51/0.98  
% 2.51/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.51/0.98  
% 2.51/0.98  fof(f19,conjecture,(
% 2.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f20,negated_conjecture,(
% 2.51/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 2.51/0.98    inference(negated_conjecture,[],[f19])).
% 2.51/0.98  
% 2.51/0.98  fof(f32,plain,(
% 2.51/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.51/0.98    inference(ennf_transformation,[],[f20])).
% 2.51/0.98  
% 2.51/0.98  fof(f33,plain,(
% 2.51/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 2.51/0.98    inference(flattening,[],[f32])).
% 2.51/0.98  
% 2.51/0.98  fof(f42,plain,(
% 2.51/0.98    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK3),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.51/0.98    introduced(choice_axiom,[])).
% 2.51/0.98  
% 2.51/0.98  fof(f41,plain,(
% 2.51/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK2,X2),X0) & v1_tops_2(sK2,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.51/0.98    introduced(choice_axiom,[])).
% 2.51/0.98  
% 2.51/0.98  fof(f40,plain,(
% 2.51/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),X1,X2),sK1) & v1_tops_2(X1,sK1) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & l1_pre_topc(sK1))),
% 2.51/0.98    introduced(choice_axiom,[])).
% 2.51/0.98  
% 2.51/0.98  fof(f43,plain,(
% 2.51/0.98    ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) & v1_tops_2(sK2,sK1) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & l1_pre_topc(sK1)),
% 2.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42,f41,f40])).
% 2.51/0.98  
% 2.51/0.98  fof(f68,plain,(
% 2.51/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f14,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f26,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.51/0.98    inference(ennf_transformation,[],[f14])).
% 2.51/0.98  
% 2.51/0.98  fof(f62,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.51/0.98    inference(cnf_transformation,[],[f26])).
% 2.51/0.98  
% 2.51/0.98  fof(f2,axiom,(
% 2.51/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f47,plain,(
% 2.51/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.51/0.98    inference(cnf_transformation,[],[f2])).
% 2.51/0.98  
% 2.51/0.98  fof(f15,axiom,(
% 2.51/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f63,plain,(
% 2.51/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.51/0.98    inference(cnf_transformation,[],[f15])).
% 2.51/0.98  
% 2.51/0.98  fof(f6,axiom,(
% 2.51/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f51,plain,(
% 2.51/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f6])).
% 2.51/0.98  
% 2.51/0.98  fof(f7,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f52,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f7])).
% 2.51/0.98  
% 2.51/0.98  fof(f8,axiom,(
% 2.51/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f53,plain,(
% 2.51/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f8])).
% 2.51/0.98  
% 2.51/0.98  fof(f9,axiom,(
% 2.51/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f54,plain,(
% 2.51/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f9])).
% 2.51/0.98  
% 2.51/0.98  fof(f10,axiom,(
% 2.51/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f55,plain,(
% 2.51/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f10])).
% 2.51/0.98  
% 2.51/0.98  fof(f11,axiom,(
% 2.51/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f56,plain,(
% 2.51/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f11])).
% 2.51/0.98  
% 2.51/0.98  fof(f72,plain,(
% 2.51/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.51/0.98    inference(definition_unfolding,[],[f55,f56])).
% 2.51/0.98  
% 2.51/0.98  fof(f73,plain,(
% 2.51/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.51/0.98    inference(definition_unfolding,[],[f54,f72])).
% 2.51/0.98  
% 2.51/0.98  fof(f74,plain,(
% 2.51/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.51/0.98    inference(definition_unfolding,[],[f53,f73])).
% 2.51/0.98  
% 2.51/0.98  fof(f75,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.51/0.98    inference(definition_unfolding,[],[f52,f74])).
% 2.51/0.98  
% 2.51/0.98  fof(f76,plain,(
% 2.51/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.51/0.98    inference(definition_unfolding,[],[f51,f75])).
% 2.51/0.98  
% 2.51/0.98  fof(f77,plain,(
% 2.51/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.51/0.98    inference(definition_unfolding,[],[f63,f76])).
% 2.51/0.98  
% 2.51/0.98  fof(f78,plain,(
% 2.51/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.51/0.98    inference(definition_unfolding,[],[f47,f77])).
% 2.51/0.98  
% 2.51/0.98  fof(f80,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.51/0.98    inference(definition_unfolding,[],[f62,f78])).
% 2.51/0.98  
% 2.51/0.98  fof(f4,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f22,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.51/0.98    inference(ennf_transformation,[],[f4])).
% 2.51/0.98  
% 2.51/0.98  fof(f23,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.51/0.98    inference(flattening,[],[f22])).
% 2.51/0.98  
% 2.51/0.98  fof(f49,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f23])).
% 2.51/0.98  
% 2.51/0.98  fof(f3,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f21,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.51/0.98    inference(ennf_transformation,[],[f3])).
% 2.51/0.98  
% 2.51/0.98  fof(f48,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f21])).
% 2.51/0.98  
% 2.51/0.98  fof(f79,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 2.51/0.98    inference(definition_unfolding,[],[f48,f77])).
% 2.51/0.98  
% 2.51/0.98  fof(f12,axiom,(
% 2.51/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f36,plain,(
% 2.51/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.51/0.98    inference(nnf_transformation,[],[f12])).
% 2.51/0.98  
% 2.51/0.98  fof(f37,plain,(
% 2.51/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.51/0.98    inference(rectify,[],[f36])).
% 2.51/0.98  
% 2.51/0.98  fof(f38,plain,(
% 2.51/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.51/0.98    introduced(choice_axiom,[])).
% 2.51/0.98  
% 2.51/0.98  fof(f39,plain,(
% 2.51/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.51/0.98  
% 2.51/0.98  fof(f58,plain,(
% 2.51/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.51/0.98    inference(cnf_transformation,[],[f39])).
% 2.51/0.98  
% 2.51/0.98  fof(f83,plain,(
% 2.51/0.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.51/0.98    inference(equality_resolution,[],[f58])).
% 2.51/0.98  
% 2.51/0.98  fof(f16,axiom,(
% 2.51/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f27,plain,(
% 2.51/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.51/0.98    inference(ennf_transformation,[],[f16])).
% 2.51/0.98  
% 2.51/0.98  fof(f64,plain,(
% 2.51/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f27])).
% 2.51/0.98  
% 2.51/0.98  fof(f18,axiom,(
% 2.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f30,plain,(
% 2.51/0.98    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.51/0.98    inference(ennf_transformation,[],[f18])).
% 2.51/0.98  
% 2.51/0.98  fof(f31,plain,(
% 2.51/0.98    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.51/0.98    inference(flattening,[],[f30])).
% 2.51/0.98  
% 2.51/0.98  fof(f66,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f31])).
% 2.51/0.98  
% 2.51/0.98  fof(f67,plain,(
% 2.51/0.98    l1_pre_topc(sK1)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f70,plain,(
% 2.51/0.98    v1_tops_2(sK2,sK1)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  fof(f13,axiom,(
% 2.51/0.98    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f61,plain,(
% 2.51/0.98    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.51/0.98    inference(cnf_transformation,[],[f13])).
% 2.51/0.98  
% 2.51/0.98  fof(f17,axiom,(
% 2.51/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f28,plain,(
% 2.51/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.51/0.98    inference(ennf_transformation,[],[f17])).
% 2.51/0.98  
% 2.51/0.98  fof(f29,plain,(
% 2.51/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.51/0.98    inference(flattening,[],[f28])).
% 2.51/0.98  
% 2.51/0.98  fof(f65,plain,(
% 2.51/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f29])).
% 2.51/0.98  
% 2.51/0.98  fof(f57,plain,(
% 2.51/0.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.51/0.98    inference(cnf_transformation,[],[f39])).
% 2.51/0.98  
% 2.51/0.98  fof(f84,plain,(
% 2.51/0.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.51/0.98    inference(equality_resolution,[],[f57])).
% 2.51/0.98  
% 2.51/0.98  fof(f5,axiom,(
% 2.51/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f24,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.51/0.98    inference(ennf_transformation,[],[f5])).
% 2.51/0.98  
% 2.51/0.98  fof(f25,plain,(
% 2.51/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.51/0.98    inference(flattening,[],[f24])).
% 2.51/0.98  
% 2.51/0.98  fof(f50,plain,(
% 2.51/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.51/0.98    inference(cnf_transformation,[],[f25])).
% 2.51/0.98  
% 2.51/0.98  fof(f1,axiom,(
% 2.51/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/0.98  
% 2.51/0.98  fof(f34,plain,(
% 2.51/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.51/0.98    inference(nnf_transformation,[],[f1])).
% 2.51/0.98  
% 2.51/0.98  fof(f35,plain,(
% 2.51/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.51/0.98    inference(flattening,[],[f34])).
% 2.51/0.98  
% 2.51/0.98  fof(f45,plain,(
% 2.51/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.51/0.98    inference(cnf_transformation,[],[f35])).
% 2.51/0.98  
% 2.51/0.98  fof(f81,plain,(
% 2.51/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.51/0.98    inference(equality_resolution,[],[f45])).
% 2.51/0.98  
% 2.51/0.98  fof(f71,plain,(
% 2.51/0.98    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1)),
% 2.51/0.98    inference(cnf_transformation,[],[f43])).
% 2.51/0.98  
% 2.51/0.98  cnf(c_18,negated_conjecture,
% 2.51/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 2.51/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1056,plain,
% 2.51/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_11,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.51/0.98      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.51/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1061,plain,
% 2.51/0.98      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2333,plain,
% 2.51/0.98      ( k5_xboole_0(sK2,k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0) ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1056,c_1061]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4,plain,
% 2.51/0.98      ( ~ r1_tarski(X0,X1)
% 2.51/0.98      | ~ r1_tarski(X2,X1)
% 2.51/0.98      | r1_tarski(k5_xboole_0(X0,X2),X1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1067,plain,
% 2.51/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.51/0.98      | r1_tarski(X2,X1) != iProver_top
% 2.51/0.98      | r1_tarski(k5_xboole_0(X0,X2),X1) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2926,plain,
% 2.51/0.98      ( r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),X1) = iProver_top
% 2.51/0.98      | r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)),X1) != iProver_top
% 2.51/0.98      | r1_tarski(sK2,X1) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_2333,c_1067]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_3,plain,
% 2.51/0.98      ( ~ r1_tarski(X0,X1)
% 2.51/0.98      | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1068,plain,
% 2.51/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.51/0.98      | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4354,plain,
% 2.51/0.98      ( r1_tarski(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),X1) = iProver_top
% 2.51/0.98      | r1_tarski(sK2,X1) != iProver_top ),
% 2.51/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_2926,c_1068]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_8,plain,
% 2.51/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1063,plain,
% 2.51/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.51/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_12,plain,
% 2.51/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1060,plain,
% 2.51/0.98      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1668,plain,
% 2.51/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.51/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1063,c_1060]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_14,plain,
% 2.51/0.98      ( ~ v1_tops_2(X0,X1)
% 2.51/0.98      | v1_tops_2(X2,X1)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.51/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.51/0.98      | ~ r1_tarski(X2,X0)
% 2.51/0.98      | ~ l1_pre_topc(X1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_19,negated_conjecture,
% 2.51/0.98      ( l1_pre_topc(sK1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_276,plain,
% 2.51/0.98      ( ~ v1_tops_2(X0,X1)
% 2.51/0.98      | v1_tops_2(X2,X1)
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.51/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.51/0.98      | ~ r1_tarski(X2,X0)
% 2.51/0.98      | sK1 != X1 ),
% 2.51/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_277,plain,
% 2.51/0.98      ( ~ v1_tops_2(X0,sK1)
% 2.51/0.98      | v1_tops_2(X1,sK1)
% 2.51/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.51/0.98      | ~ r1_tarski(X1,X0) ),
% 2.51/0.98      inference(unflattening,[status(thm)],[c_276]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1055,plain,
% 2.51/0.98      ( v1_tops_2(X0,sK1) != iProver_top
% 2.51/0.98      | v1_tops_2(X1,sK1) = iProver_top
% 2.51/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.51/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2015,plain,
% 2.51/0.98      ( v1_tops_2(X0,sK1) != iProver_top
% 2.51/0.98      | v1_tops_2(X1,sK1) = iProver_top
% 2.51/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.51/0.98      | r1_tarski(X1,X0) != iProver_top
% 2.51/0.98      | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1668,c_1055]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2208,plain,
% 2.51/0.98      ( v1_tops_2(X0,sK1) = iProver_top
% 2.51/0.98      | v1_tops_2(sK2,sK1) != iProver_top
% 2.51/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.51/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1056,c_2015]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_16,negated_conjecture,
% 2.51/0.98      ( v1_tops_2(sK2,sK1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_23,plain,
% 2.51/0.98      ( v1_tops_2(sK2,sK1) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_10,plain,
% 2.51/0.98      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.51/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_13,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_261,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 2.51/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_262,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.51/0.98      inference(unflattening,[status(thm)],[c_261]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_9,plain,
% 2.51/0.98      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_459,plain,
% 2.51/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.51/0.98      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_460,plain,
% 2.51/0.98      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.51/0.98      inference(renaming,[status(thm)],[c_459]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_494,plain,
% 2.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.51/0.98      inference(bin_hyper_res,[status(thm)],[c_262,c_460]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1054,plain,
% 2.51/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.51/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1521,plain,
% 2.51/0.98      ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1056,c_1054]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_5,plain,
% 2.51/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.51/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1636,plain,
% 2.51/0.98      ( ~ r1_tarski(X0,X1)
% 2.51/0.98      | ~ r1_tarski(X1,k1_zfmisc_1(X2))
% 2.51/0.98      | r1_tarski(X0,k1_zfmisc_1(X2)) ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2872,plain,
% 2.51/0.98      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/0.98      | ~ r1_tarski(X0,sK2)
% 2.51/0.98      | ~ r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_1636]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2873,plain,
% 2.51/0.98      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.51/0.98      | r1_tarski(X0,sK2) != iProver_top
% 2.51/0.98      | r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_2872]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_3001,plain,
% 2.51/0.98      ( v1_tops_2(X0,sK1) = iProver_top | r1_tarski(X0,sK2) != iProver_top ),
% 2.51/0.98      inference(global_propositional_subsumption,
% 2.51/0.98                [status(thm)],
% 2.51/0.98                [c_2208,c_23,c_1521,c_2873]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4360,plain,
% 2.51/0.98      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),sK1) = iProver_top
% 2.51/0.98      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_4354,c_3001]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f81]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1420,plain,
% 2.51/0.98      ( r1_tarski(sK2,sK2) ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1423,plain,
% 2.51/0.98      ( r1_tarski(sK2,sK2) = iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_1420]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1426,plain,
% 2.51/0.98      ( ~ r1_tarski(X0,sK2)
% 2.51/0.98      | r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),sK2) ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2380,plain,
% 2.51/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)),sK2)
% 2.51/0.98      | ~ r1_tarski(sK2,sK2) ),
% 2.51/0.98      inference(instantiation,[status(thm)],[c_1426]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_2381,plain,
% 2.51/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)),sK2) = iProver_top
% 2.51/0.98      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_2380]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_3011,plain,
% 2.51/0.98      ( v1_tops_2(k5_xboole_0(X0,X1),sK1) = iProver_top
% 2.51/0.98      | r1_tarski(X0,sK2) != iProver_top
% 2.51/0.98      | r1_tarski(X1,sK2) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_1067,c_3001]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_3377,plain,
% 2.51/0.98      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),sK1) = iProver_top
% 2.51/0.98      | r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)),sK2) != iProver_top
% 2.51/0.98      | r1_tarski(sK2,sK2) != iProver_top ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_2333,c_3011]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4397,plain,
% 2.51/0.98      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,X0),sK1) = iProver_top ),
% 2.51/0.98      inference(global_propositional_subsumption,
% 2.51/0.98                [status(thm)],
% 2.51/0.98                [c_4360,c_1423,c_2381,c_3377]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_15,negated_conjecture,
% 2.51/0.98      ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) ),
% 2.51/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_1059,plain,
% 2.51/0.98      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK2,sK3),sK1) != iProver_top ),
% 2.51/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.51/0.98  
% 2.51/0.98  cnf(c_4404,plain,
% 2.51/0.98      ( $false ),
% 2.51/0.98      inference(superposition,[status(thm)],[c_4397,c_1059]) ).
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.51/0.98  
% 2.51/0.98  ------                               Statistics
% 2.51/0.98  
% 2.51/0.98  ------ General
% 2.51/0.98  
% 2.51/0.98  abstr_ref_over_cycles:                  0
% 2.51/0.98  abstr_ref_under_cycles:                 0
% 2.51/0.98  gc_basic_clause_elim:                   0
% 2.51/0.98  forced_gc_time:                         0
% 2.51/0.98  parsing_time:                           0.01
% 2.51/0.98  unif_index_cands_time:                  0.
% 2.51/0.98  unif_index_add_time:                    0.
% 2.51/0.98  orderings_time:                         0.
% 2.51/0.98  out_proof_time:                         0.009
% 2.51/0.98  total_time:                             0.139
% 2.51/0.98  num_of_symbols:                         47
% 2.51/0.98  num_of_terms:                           3492
% 2.51/0.98  
% 2.51/0.98  ------ Preprocessing
% 2.51/0.98  
% 2.51/0.98  num_of_splits:                          0
% 2.51/0.98  num_of_split_atoms:                     0
% 2.51/0.98  num_of_reused_defs:                     0
% 2.51/0.98  num_eq_ax_congr_red:                    36
% 2.51/0.98  num_of_sem_filtered_clauses:            1
% 2.51/0.98  num_of_subtypes:                        0
% 2.51/0.98  monotx_restored_types:                  0
% 2.51/0.98  sat_num_of_epr_types:                   0
% 2.51/0.98  sat_num_of_non_cyclic_types:            0
% 2.51/0.98  sat_guarded_non_collapsed_types:        0
% 2.51/0.98  num_pure_diseq_elim:                    0
% 2.51/0.98  simp_replaced_by:                       0
% 2.51/0.98  res_preprocessed:                       93
% 2.51/0.98  prep_upred:                             0
% 2.51/0.98  prep_unflattend:                        22
% 2.51/0.98  smt_new_axioms:                         0
% 2.51/0.98  pred_elim_cands:                        4
% 2.51/0.98  pred_elim:                              2
% 2.51/0.98  pred_elim_cl:                           2
% 2.51/0.98  pred_elim_cycles:                       4
% 2.51/0.98  merged_defs:                            8
% 2.51/0.98  merged_defs_ncl:                        0
% 2.51/0.98  bin_hyper_res:                          9
% 2.51/0.98  prep_cycles:                            4
% 2.51/0.98  pred_elim_time:                         0.004
% 2.51/0.98  splitting_time:                         0.
% 2.51/0.98  sem_filter_time:                        0.
% 2.51/0.98  monotx_time:                            0.
% 2.51/0.98  subtype_inf_time:                       0.
% 2.51/0.98  
% 2.51/0.98  ------ Problem properties
% 2.51/0.98  
% 2.51/0.98  clauses:                                17
% 2.51/0.98  conjectures:                            4
% 2.51/0.98  epr:                                    5
% 2.51/0.98  horn:                                   16
% 2.51/0.98  ground:                                 4
% 2.51/0.98  unary:                                  5
% 2.51/0.98  binary:                                 6
% 2.51/0.98  lits:                                   37
% 2.51/0.98  lits_eq:                                4
% 2.51/0.98  fd_pure:                                0
% 2.51/0.98  fd_pseudo:                              0
% 2.51/0.98  fd_cond:                                0
% 2.51/0.98  fd_pseudo_cond:                         3
% 2.51/0.98  ac_symbols:                             0
% 2.51/0.98  
% 2.51/0.98  ------ Propositional Solver
% 2.51/0.98  
% 2.51/0.98  prop_solver_calls:                      27
% 2.51/0.98  prop_fast_solver_calls:                 581
% 2.51/0.98  smt_solver_calls:                       0
% 2.51/0.98  smt_fast_solver_calls:                  0
% 2.51/0.98  prop_num_of_clauses:                    1364
% 2.51/0.98  prop_preprocess_simplified:             4121
% 2.51/0.98  prop_fo_subsumed:                       6
% 2.51/0.98  prop_solver_time:                       0.
% 2.51/0.98  smt_solver_time:                        0.
% 2.51/0.98  smt_fast_solver_time:                   0.
% 2.51/0.98  prop_fast_solver_time:                  0.
% 2.51/0.98  prop_unsat_core_time:                   0.
% 2.51/0.98  
% 2.51/0.98  ------ QBF
% 2.51/0.98  
% 2.51/0.98  qbf_q_res:                              0
% 2.51/0.98  qbf_num_tautologies:                    0
% 2.51/0.98  qbf_prep_cycles:                        0
% 2.51/0.98  
% 2.51/0.98  ------ BMC1
% 2.51/0.98  
% 2.51/0.98  bmc1_current_bound:                     -1
% 2.51/0.98  bmc1_last_solved_bound:                 -1
% 2.51/0.98  bmc1_unsat_core_size:                   -1
% 2.51/0.98  bmc1_unsat_core_parents_size:           -1
% 2.51/0.98  bmc1_merge_next_fun:                    0
% 2.51/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.51/0.98  
% 2.51/0.98  ------ Instantiation
% 2.51/0.98  
% 2.51/0.98  inst_num_of_clauses:                    365
% 2.51/0.98  inst_num_in_passive:                    60
% 2.51/0.98  inst_num_in_active:                     186
% 2.51/0.98  inst_num_in_unprocessed:                120
% 2.51/0.98  inst_num_of_loops:                      210
% 2.51/0.98  inst_num_of_learning_restarts:          0
% 2.51/0.98  inst_num_moves_active_passive:          21
% 2.51/0.98  inst_lit_activity:                      0
% 2.51/0.98  inst_lit_activity_moves:                0
% 2.51/0.98  inst_num_tautologies:                   0
% 2.51/0.98  inst_num_prop_implied:                  0
% 2.51/0.98  inst_num_existing_simplified:           0
% 2.51/0.98  inst_num_eq_res_simplified:             0
% 2.51/0.98  inst_num_child_elim:                    0
% 2.51/0.98  inst_num_of_dismatching_blockings:      287
% 2.51/0.98  inst_num_of_non_proper_insts:           449
% 2.51/0.98  inst_num_of_duplicates:                 0
% 2.51/0.98  inst_inst_num_from_inst_to_res:         0
% 2.51/0.98  inst_dismatching_checking_time:         0.
% 2.51/0.98  
% 2.51/0.98  ------ Resolution
% 2.51/0.98  
% 2.51/0.98  res_num_of_clauses:                     0
% 2.51/0.98  res_num_in_passive:                     0
% 2.51/0.98  res_num_in_active:                      0
% 2.51/0.98  res_num_of_loops:                       97
% 2.51/0.98  res_forward_subset_subsumed:            35
% 2.51/0.98  res_backward_subset_subsumed:           2
% 2.51/0.98  res_forward_subsumed:                   0
% 2.51/0.98  res_backward_subsumed:                  0
% 2.51/0.98  res_forward_subsumption_resolution:     0
% 2.51/0.98  res_backward_subsumption_resolution:    0
% 2.51/0.98  res_clause_to_clause_subsumption:       324
% 2.51/0.98  res_orphan_elimination:                 0
% 2.51/0.98  res_tautology_del:                      50
% 2.51/0.98  res_num_eq_res_simplified:              0
% 2.51/0.98  res_num_sel_changes:                    0
% 2.51/0.98  res_moves_from_active_to_pass:          0
% 2.51/0.98  
% 2.51/0.98  ------ Superposition
% 2.51/0.98  
% 2.51/0.98  sup_time_total:                         0.
% 2.51/0.98  sup_time_generating:                    0.
% 2.51/0.98  sup_time_sim_full:                      0.
% 2.51/0.98  sup_time_sim_immed:                     0.
% 2.51/0.98  
% 2.51/0.98  sup_num_of_clauses:                     77
% 2.51/0.98  sup_num_in_active:                      42
% 2.51/0.98  sup_num_in_passive:                     35
% 2.51/0.98  sup_num_of_loops:                       41
% 2.51/0.98  sup_fw_superposition:                   29
% 2.51/0.98  sup_bw_superposition:                   48
% 2.51/0.98  sup_immediate_simplified:               2
% 2.51/0.98  sup_given_eliminated:                   0
% 2.51/0.98  comparisons_done:                       0
% 2.51/0.98  comparisons_avoided:                    0
% 2.51/0.98  
% 2.51/0.98  ------ Simplifications
% 2.51/0.98  
% 2.51/0.98  
% 2.51/0.98  sim_fw_subset_subsumed:                 1
% 2.51/0.98  sim_bw_subset_subsumed:                 1
% 2.51/0.98  sim_fw_subsumed:                        1
% 2.51/0.98  sim_bw_subsumed:                        0
% 2.51/0.98  sim_fw_subsumption_res:                 2
% 2.51/0.98  sim_bw_subsumption_res:                 0
% 2.51/0.98  sim_tautology_del:                      6
% 2.51/0.98  sim_eq_tautology_del:                   2
% 2.51/0.98  sim_eq_res_simp:                        0
% 2.51/0.98  sim_fw_demodulated:                     0
% 2.51/0.98  sim_bw_demodulated:                     0
% 2.51/0.98  sim_light_normalised:                   0
% 2.51/0.98  sim_joinable_taut:                      0
% 2.51/0.98  sim_joinable_simp:                      0
% 2.51/0.98  sim_ac_normalised:                      0
% 2.51/0.98  sim_smt_subsumption:                    0
% 2.51/0.98  
%------------------------------------------------------------------------------
