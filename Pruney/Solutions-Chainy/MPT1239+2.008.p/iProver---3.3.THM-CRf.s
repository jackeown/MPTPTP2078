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
% DateTime   : Thu Dec  3 12:13:54 EST 2020

% Result     : Theorem 12.13s
% Output     : CNFRefutation 12.13s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 252 expanded)
%              Number of clauses        :   77 (  97 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  322 ( 809 expanded)
%              Number of equality atoms :   98 ( 125 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32,f31,f30])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1078,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k7_subset_1(u1_struct_0(sK0),sK1,X2)
    | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_9643,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k7_subset_1(u1_struct_0(sK0),sK1,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_25502,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(sK1,X0) != k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9643])).

cnf(c_52078,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(sK1,sK2) != k7_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_25502])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1139,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_43023,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_732,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_738,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_733,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_736,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3097,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),X1) = k4_xboole_0(k1_tops_1(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_736])).

cnf(c_7882,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_733,c_3097])).

cnf(c_3096,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_733,c_736])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_735,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3270,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3096,c_735])).

cnf(c_8034,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7882,c_3270])).

cnf(c_8055,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_8034])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_734,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_731,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_960,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_731])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_743,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1420,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_960,c_743])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_737,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3272,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3096,c_737])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5349,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3272,c_21])).

cnf(c_5360,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5349,c_731])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_745,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6262,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5360,c_745])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_740,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8811,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,k2_xboole_0(X0,X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6262,c_740])).

cnf(c_12059,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_8811])).

cnf(c_39249,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8055,c_12059])).

cnf(c_39254,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_39249])).

cnf(c_39255,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_39254])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_886,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_34949,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2491,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X0)
    | k4_xboole_0(X1,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7776,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))
    | ~ r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))
    | k4_xboole_0(X2,X1) = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2491])).

cnf(c_21550,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK2))
    | k4_xboole_0(X0,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_7776])).

cnf(c_34948,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
    | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_21550])).

cnf(c_404,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2501,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X3) != X1
    | k4_xboole_0(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_6083,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) = X0
    | k4_xboole_0(X1,X2) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_12244,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) != k4_xboole_0(sK1,X0)
    | k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | k4_xboole_0(sK1,X0) != k4_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_6083])).

cnf(c_32561,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_12244])).

cnf(c_920,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10076,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_403,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3227,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_930,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3219,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52078,c_43023,c_39255,c_34949,c_34948,c_32561,c_10076,c_3227,c_3219,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:01:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 12.13/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.13/1.99  
% 12.13/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.13/1.99  
% 12.13/1.99  ------  iProver source info
% 12.13/1.99  
% 12.13/1.99  git: date: 2020-06-30 10:37:57 +0100
% 12.13/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.13/1.99  git: non_committed_changes: false
% 12.13/1.99  git: last_make_outside_of_git: false
% 12.13/1.99  
% 12.13/1.99  ------ 
% 12.13/1.99  
% 12.13/1.99  ------ Input Options
% 12.13/1.99  
% 12.13/1.99  --out_options                           all
% 12.13/1.99  --tptp_safe_out                         true
% 12.13/1.99  --problem_path                          ""
% 12.13/1.99  --include_path                          ""
% 12.13/1.99  --clausifier                            res/vclausify_rel
% 12.13/1.99  --clausifier_options                    --mode clausify
% 12.13/1.99  --stdin                                 false
% 12.13/1.99  --stats_out                             all
% 12.13/1.99  
% 12.13/1.99  ------ General Options
% 12.13/1.99  
% 12.13/1.99  --fof                                   false
% 12.13/1.99  --time_out_real                         305.
% 12.13/1.99  --time_out_virtual                      -1.
% 12.13/1.99  --symbol_type_check                     false
% 12.13/1.99  --clausify_out                          false
% 12.13/1.99  --sig_cnt_out                           false
% 12.13/1.99  --trig_cnt_out                          false
% 12.13/1.99  --trig_cnt_out_tolerance                1.
% 12.13/1.99  --trig_cnt_out_sk_spl                   false
% 12.13/1.99  --abstr_cl_out                          false
% 12.13/1.99  
% 12.13/1.99  ------ Global Options
% 12.13/1.99  
% 12.13/1.99  --schedule                              default
% 12.13/1.99  --add_important_lit                     false
% 12.13/1.99  --prop_solver_per_cl                    1000
% 12.13/1.99  --min_unsat_core                        false
% 12.13/1.99  --soft_assumptions                      false
% 12.13/1.99  --soft_lemma_size                       3
% 12.13/1.99  --prop_impl_unit_size                   0
% 12.13/1.99  --prop_impl_unit                        []
% 12.13/1.99  --share_sel_clauses                     true
% 12.13/1.99  --reset_solvers                         false
% 12.13/1.99  --bc_imp_inh                            [conj_cone]
% 12.13/1.99  --conj_cone_tolerance                   3.
% 12.13/1.99  --extra_neg_conj                        none
% 12.13/1.99  --large_theory_mode                     true
% 12.13/1.99  --prolific_symb_bound                   200
% 12.13/1.99  --lt_threshold                          2000
% 12.13/1.99  --clause_weak_htbl                      true
% 12.13/1.99  --gc_record_bc_elim                     false
% 12.13/1.99  
% 12.13/1.99  ------ Preprocessing Options
% 12.13/1.99  
% 12.13/1.99  --preprocessing_flag                    true
% 12.13/1.99  --time_out_prep_mult                    0.1
% 12.13/1.99  --splitting_mode                        input
% 12.13/1.99  --splitting_grd                         true
% 12.13/1.99  --splitting_cvd                         false
% 12.13/1.99  --splitting_cvd_svl                     false
% 12.13/1.99  --splitting_nvd                         32
% 12.13/1.99  --sub_typing                            true
% 12.13/1.99  --prep_gs_sim                           true
% 12.13/1.99  --prep_unflatten                        true
% 12.13/1.99  --prep_res_sim                          true
% 12.13/1.99  --prep_upred                            true
% 12.13/1.99  --prep_sem_filter                       exhaustive
% 12.13/1.99  --prep_sem_filter_out                   false
% 12.13/1.99  --pred_elim                             true
% 12.13/1.99  --res_sim_input                         true
% 12.13/1.99  --eq_ax_congr_red                       true
% 12.13/1.99  --pure_diseq_elim                       true
% 12.13/1.99  --brand_transform                       false
% 12.13/1.99  --non_eq_to_eq                          false
% 12.13/1.99  --prep_def_merge                        true
% 12.13/1.99  --prep_def_merge_prop_impl              false
% 12.13/1.99  --prep_def_merge_mbd                    true
% 12.13/1.99  --prep_def_merge_tr_red                 false
% 12.13/1.99  --prep_def_merge_tr_cl                  false
% 12.13/1.99  --smt_preprocessing                     true
% 12.13/1.99  --smt_ac_axioms                         fast
% 12.13/1.99  --preprocessed_out                      false
% 12.13/1.99  --preprocessed_stats                    false
% 12.13/1.99  
% 12.13/1.99  ------ Abstraction refinement Options
% 12.13/1.99  
% 12.13/1.99  --abstr_ref                             []
% 12.13/1.99  --abstr_ref_prep                        false
% 12.13/1.99  --abstr_ref_until_sat                   false
% 12.13/1.99  --abstr_ref_sig_restrict                funpre
% 12.13/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.13/1.99  --abstr_ref_under                       []
% 12.13/1.99  
% 12.13/1.99  ------ SAT Options
% 12.13/1.99  
% 12.13/1.99  --sat_mode                              false
% 12.13/1.99  --sat_fm_restart_options                ""
% 12.13/1.99  --sat_gr_def                            false
% 12.13/1.99  --sat_epr_types                         true
% 12.13/1.99  --sat_non_cyclic_types                  false
% 12.13/1.99  --sat_finite_models                     false
% 12.13/1.99  --sat_fm_lemmas                         false
% 12.13/1.99  --sat_fm_prep                           false
% 12.13/1.99  --sat_fm_uc_incr                        true
% 12.13/1.99  --sat_out_model                         small
% 12.13/1.99  --sat_out_clauses                       false
% 12.13/1.99  
% 12.13/1.99  ------ QBF Options
% 12.13/1.99  
% 12.13/1.99  --qbf_mode                              false
% 12.13/1.99  --qbf_elim_univ                         false
% 12.13/1.99  --qbf_dom_inst                          none
% 12.13/1.99  --qbf_dom_pre_inst                      false
% 12.13/1.99  --qbf_sk_in                             false
% 12.13/1.99  --qbf_pred_elim                         true
% 12.13/1.99  --qbf_split                             512
% 12.13/1.99  
% 12.13/1.99  ------ BMC1 Options
% 12.13/1.99  
% 12.13/1.99  --bmc1_incremental                      false
% 12.13/1.99  --bmc1_axioms                           reachable_all
% 12.13/1.99  --bmc1_min_bound                        0
% 12.13/1.99  --bmc1_max_bound                        -1
% 12.13/1.99  --bmc1_max_bound_default                -1
% 12.13/1.99  --bmc1_symbol_reachability              true
% 12.13/1.99  --bmc1_property_lemmas                  false
% 12.13/1.99  --bmc1_k_induction                      false
% 12.13/1.99  --bmc1_non_equiv_states                 false
% 12.13/1.99  --bmc1_deadlock                         false
% 12.13/1.99  --bmc1_ucm                              false
% 12.13/1.99  --bmc1_add_unsat_core                   none
% 12.13/1.99  --bmc1_unsat_core_children              false
% 12.13/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.13/1.99  --bmc1_out_stat                         full
% 12.13/1.99  --bmc1_ground_init                      false
% 12.13/1.99  --bmc1_pre_inst_next_state              false
% 12.13/1.99  --bmc1_pre_inst_state                   false
% 12.13/1.99  --bmc1_pre_inst_reach_state             false
% 12.13/1.99  --bmc1_out_unsat_core                   false
% 12.13/1.99  --bmc1_aig_witness_out                  false
% 12.13/1.99  --bmc1_verbose                          false
% 12.13/1.99  --bmc1_dump_clauses_tptp                false
% 12.13/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.13/1.99  --bmc1_dump_file                        -
% 12.13/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.13/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.13/1.99  --bmc1_ucm_extend_mode                  1
% 12.13/1.99  --bmc1_ucm_init_mode                    2
% 12.13/1.99  --bmc1_ucm_cone_mode                    none
% 12.13/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.13/1.99  --bmc1_ucm_relax_model                  4
% 12.13/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.13/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.13/1.99  --bmc1_ucm_layered_model                none
% 12.13/1.99  --bmc1_ucm_max_lemma_size               10
% 12.13/1.99  
% 12.13/1.99  ------ AIG Options
% 12.13/1.99  
% 12.13/1.99  --aig_mode                              false
% 12.13/1.99  
% 12.13/1.99  ------ Instantiation Options
% 12.13/1.99  
% 12.13/1.99  --instantiation_flag                    true
% 12.13/1.99  --inst_sos_flag                         false
% 12.13/1.99  --inst_sos_phase                        true
% 12.13/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.13/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.13/1.99  --inst_lit_sel_side                     num_symb
% 12.13/1.99  --inst_solver_per_active                1400
% 12.13/1.99  --inst_solver_calls_frac                1.
% 12.13/1.99  --inst_passive_queue_type               priority_queues
% 12.13/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.13/1.99  --inst_passive_queues_freq              [25;2]
% 12.13/1.99  --inst_dismatching                      true
% 12.13/1.99  --inst_eager_unprocessed_to_passive     true
% 12.13/1.99  --inst_prop_sim_given                   true
% 12.13/1.99  --inst_prop_sim_new                     false
% 12.13/1.99  --inst_subs_new                         false
% 12.13/1.99  --inst_eq_res_simp                      false
% 12.13/1.99  --inst_subs_given                       false
% 12.13/1.99  --inst_orphan_elimination               true
% 12.13/1.99  --inst_learning_loop_flag               true
% 12.13/1.99  --inst_learning_start                   3000
% 12.13/1.99  --inst_learning_factor                  2
% 12.13/1.99  --inst_start_prop_sim_after_learn       3
% 12.13/1.99  --inst_sel_renew                        solver
% 12.13/1.99  --inst_lit_activity_flag                true
% 12.13/1.99  --inst_restr_to_given                   false
% 12.13/1.99  --inst_activity_threshold               500
% 12.13/1.99  --inst_out_proof                        true
% 12.13/1.99  
% 12.13/1.99  ------ Resolution Options
% 12.13/1.99  
% 12.13/1.99  --resolution_flag                       true
% 12.13/1.99  --res_lit_sel                           adaptive
% 12.13/1.99  --res_lit_sel_side                      none
% 12.13/1.99  --res_ordering                          kbo
% 12.13/1.99  --res_to_prop_solver                    active
% 12.13/1.99  --res_prop_simpl_new                    false
% 12.13/1.99  --res_prop_simpl_given                  true
% 12.13/1.99  --res_passive_queue_type                priority_queues
% 12.13/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.13/1.99  --res_passive_queues_freq               [15;5]
% 12.13/1.99  --res_forward_subs                      full
% 12.13/1.99  --res_backward_subs                     full
% 12.13/1.99  --res_forward_subs_resolution           true
% 12.13/1.99  --res_backward_subs_resolution          true
% 12.13/1.99  --res_orphan_elimination                true
% 12.13/1.99  --res_time_limit                        2.
% 12.13/1.99  --res_out_proof                         true
% 12.13/1.99  
% 12.13/1.99  ------ Superposition Options
% 12.13/1.99  
% 12.13/1.99  --superposition_flag                    true
% 12.13/1.99  --sup_passive_queue_type                priority_queues
% 12.13/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.13/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.13/1.99  --demod_completeness_check              fast
% 12.13/1.99  --demod_use_ground                      true
% 12.13/1.99  --sup_to_prop_solver                    passive
% 12.13/1.99  --sup_prop_simpl_new                    true
% 12.13/1.99  --sup_prop_simpl_given                  true
% 12.13/1.99  --sup_fun_splitting                     false
% 12.13/1.99  --sup_smt_interval                      50000
% 12.13/1.99  
% 12.13/1.99  ------ Superposition Simplification Setup
% 12.13/1.99  
% 12.13/1.99  --sup_indices_passive                   []
% 12.13/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.13/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.99  --sup_full_bw                           [BwDemod]
% 12.13/1.99  --sup_immed_triv                        [TrivRules]
% 12.13/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.13/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.99  --sup_immed_bw_main                     []
% 12.13/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.13/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.13/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.13/1.99  
% 12.13/1.99  ------ Combination Options
% 12.13/1.99  
% 12.13/1.99  --comb_res_mult                         3
% 12.13/1.99  --comb_sup_mult                         2
% 12.13/1.99  --comb_inst_mult                        10
% 12.13/1.99  
% 12.13/1.99  ------ Debug Options
% 12.13/1.99  
% 12.13/1.99  --dbg_backtrace                         false
% 12.13/1.99  --dbg_dump_prop_clauses                 false
% 12.13/1.99  --dbg_dump_prop_clauses_file            -
% 12.13/1.99  --dbg_out_stat                          false
% 12.13/1.99  ------ Parsing...
% 12.13/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.13/1.99  
% 12.13/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 12.13/1.99  
% 12.13/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.13/1.99  
% 12.13/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.13/1.99  ------ Proving...
% 12.13/1.99  ------ Problem Properties 
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  clauses                                 18
% 12.13/1.99  conjectures                             3
% 12.13/1.99  EPR                                     2
% 12.13/1.99  Horn                                    18
% 12.13/1.99  unary                                   5
% 12.13/1.99  binary                                  9
% 12.13/1.99  lits                                    36
% 12.13/1.99  lits eq                                 3
% 12.13/1.99  fd_pure                                 0
% 12.13/1.99  fd_pseudo                               0
% 12.13/1.99  fd_cond                                 0
% 12.13/1.99  fd_pseudo_cond                          1
% 12.13/1.99  AC symbols                              0
% 12.13/1.99  
% 12.13/1.99  ------ Schedule dynamic 5 is on 
% 12.13/1.99  
% 12.13/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  ------ 
% 12.13/1.99  Current options:
% 12.13/1.99  ------ 
% 12.13/1.99  
% 12.13/1.99  ------ Input Options
% 12.13/1.99  
% 12.13/1.99  --out_options                           all
% 12.13/1.99  --tptp_safe_out                         true
% 12.13/1.99  --problem_path                          ""
% 12.13/1.99  --include_path                          ""
% 12.13/1.99  --clausifier                            res/vclausify_rel
% 12.13/1.99  --clausifier_options                    --mode clausify
% 12.13/1.99  --stdin                                 false
% 12.13/1.99  --stats_out                             all
% 12.13/1.99  
% 12.13/1.99  ------ General Options
% 12.13/1.99  
% 12.13/1.99  --fof                                   false
% 12.13/1.99  --time_out_real                         305.
% 12.13/1.99  --time_out_virtual                      -1.
% 12.13/1.99  --symbol_type_check                     false
% 12.13/1.99  --clausify_out                          false
% 12.13/1.99  --sig_cnt_out                           false
% 12.13/1.99  --trig_cnt_out                          false
% 12.13/1.99  --trig_cnt_out_tolerance                1.
% 12.13/1.99  --trig_cnt_out_sk_spl                   false
% 12.13/1.99  --abstr_cl_out                          false
% 12.13/1.99  
% 12.13/1.99  ------ Global Options
% 12.13/1.99  
% 12.13/1.99  --schedule                              default
% 12.13/1.99  --add_important_lit                     false
% 12.13/1.99  --prop_solver_per_cl                    1000
% 12.13/1.99  --min_unsat_core                        false
% 12.13/1.99  --soft_assumptions                      false
% 12.13/1.99  --soft_lemma_size                       3
% 12.13/1.99  --prop_impl_unit_size                   0
% 12.13/1.99  --prop_impl_unit                        []
% 12.13/1.99  --share_sel_clauses                     true
% 12.13/1.99  --reset_solvers                         false
% 12.13/1.99  --bc_imp_inh                            [conj_cone]
% 12.13/1.99  --conj_cone_tolerance                   3.
% 12.13/1.99  --extra_neg_conj                        none
% 12.13/1.99  --large_theory_mode                     true
% 12.13/1.99  --prolific_symb_bound                   200
% 12.13/1.99  --lt_threshold                          2000
% 12.13/1.99  --clause_weak_htbl                      true
% 12.13/1.99  --gc_record_bc_elim                     false
% 12.13/1.99  
% 12.13/1.99  ------ Preprocessing Options
% 12.13/1.99  
% 12.13/1.99  --preprocessing_flag                    true
% 12.13/1.99  --time_out_prep_mult                    0.1
% 12.13/1.99  --splitting_mode                        input
% 12.13/1.99  --splitting_grd                         true
% 12.13/1.99  --splitting_cvd                         false
% 12.13/1.99  --splitting_cvd_svl                     false
% 12.13/1.99  --splitting_nvd                         32
% 12.13/1.99  --sub_typing                            true
% 12.13/1.99  --prep_gs_sim                           true
% 12.13/1.99  --prep_unflatten                        true
% 12.13/1.99  --prep_res_sim                          true
% 12.13/1.99  --prep_upred                            true
% 12.13/1.99  --prep_sem_filter                       exhaustive
% 12.13/1.99  --prep_sem_filter_out                   false
% 12.13/1.99  --pred_elim                             true
% 12.13/1.99  --res_sim_input                         true
% 12.13/1.99  --eq_ax_congr_red                       true
% 12.13/1.99  --pure_diseq_elim                       true
% 12.13/1.99  --brand_transform                       false
% 12.13/1.99  --non_eq_to_eq                          false
% 12.13/1.99  --prep_def_merge                        true
% 12.13/1.99  --prep_def_merge_prop_impl              false
% 12.13/1.99  --prep_def_merge_mbd                    true
% 12.13/1.99  --prep_def_merge_tr_red                 false
% 12.13/1.99  --prep_def_merge_tr_cl                  false
% 12.13/1.99  --smt_preprocessing                     true
% 12.13/1.99  --smt_ac_axioms                         fast
% 12.13/1.99  --preprocessed_out                      false
% 12.13/1.99  --preprocessed_stats                    false
% 12.13/1.99  
% 12.13/1.99  ------ Abstraction refinement Options
% 12.13/1.99  
% 12.13/1.99  --abstr_ref                             []
% 12.13/1.99  --abstr_ref_prep                        false
% 12.13/1.99  --abstr_ref_until_sat                   false
% 12.13/1.99  --abstr_ref_sig_restrict                funpre
% 12.13/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.13/1.99  --abstr_ref_under                       []
% 12.13/1.99  
% 12.13/1.99  ------ SAT Options
% 12.13/1.99  
% 12.13/1.99  --sat_mode                              false
% 12.13/1.99  --sat_fm_restart_options                ""
% 12.13/1.99  --sat_gr_def                            false
% 12.13/1.99  --sat_epr_types                         true
% 12.13/1.99  --sat_non_cyclic_types                  false
% 12.13/1.99  --sat_finite_models                     false
% 12.13/1.99  --sat_fm_lemmas                         false
% 12.13/1.99  --sat_fm_prep                           false
% 12.13/1.99  --sat_fm_uc_incr                        true
% 12.13/1.99  --sat_out_model                         small
% 12.13/1.99  --sat_out_clauses                       false
% 12.13/1.99  
% 12.13/1.99  ------ QBF Options
% 12.13/1.99  
% 12.13/1.99  --qbf_mode                              false
% 12.13/1.99  --qbf_elim_univ                         false
% 12.13/1.99  --qbf_dom_inst                          none
% 12.13/1.99  --qbf_dom_pre_inst                      false
% 12.13/1.99  --qbf_sk_in                             false
% 12.13/1.99  --qbf_pred_elim                         true
% 12.13/1.99  --qbf_split                             512
% 12.13/1.99  
% 12.13/1.99  ------ BMC1 Options
% 12.13/1.99  
% 12.13/1.99  --bmc1_incremental                      false
% 12.13/1.99  --bmc1_axioms                           reachable_all
% 12.13/1.99  --bmc1_min_bound                        0
% 12.13/1.99  --bmc1_max_bound                        -1
% 12.13/1.99  --bmc1_max_bound_default                -1
% 12.13/1.99  --bmc1_symbol_reachability              true
% 12.13/1.99  --bmc1_property_lemmas                  false
% 12.13/1.99  --bmc1_k_induction                      false
% 12.13/1.99  --bmc1_non_equiv_states                 false
% 12.13/1.99  --bmc1_deadlock                         false
% 12.13/1.99  --bmc1_ucm                              false
% 12.13/1.99  --bmc1_add_unsat_core                   none
% 12.13/1.99  --bmc1_unsat_core_children              false
% 12.13/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.13/1.99  --bmc1_out_stat                         full
% 12.13/1.99  --bmc1_ground_init                      false
% 12.13/1.99  --bmc1_pre_inst_next_state              false
% 12.13/1.99  --bmc1_pre_inst_state                   false
% 12.13/1.99  --bmc1_pre_inst_reach_state             false
% 12.13/1.99  --bmc1_out_unsat_core                   false
% 12.13/1.99  --bmc1_aig_witness_out                  false
% 12.13/1.99  --bmc1_verbose                          false
% 12.13/1.99  --bmc1_dump_clauses_tptp                false
% 12.13/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.13/1.99  --bmc1_dump_file                        -
% 12.13/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.13/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.13/1.99  --bmc1_ucm_extend_mode                  1
% 12.13/1.99  --bmc1_ucm_init_mode                    2
% 12.13/1.99  --bmc1_ucm_cone_mode                    none
% 12.13/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.13/1.99  --bmc1_ucm_relax_model                  4
% 12.13/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.13/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.13/1.99  --bmc1_ucm_layered_model                none
% 12.13/1.99  --bmc1_ucm_max_lemma_size               10
% 12.13/1.99  
% 12.13/1.99  ------ AIG Options
% 12.13/1.99  
% 12.13/1.99  --aig_mode                              false
% 12.13/1.99  
% 12.13/1.99  ------ Instantiation Options
% 12.13/1.99  
% 12.13/1.99  --instantiation_flag                    true
% 12.13/1.99  --inst_sos_flag                         false
% 12.13/1.99  --inst_sos_phase                        true
% 12.13/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.13/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.13/1.99  --inst_lit_sel_side                     none
% 12.13/1.99  --inst_solver_per_active                1400
% 12.13/1.99  --inst_solver_calls_frac                1.
% 12.13/1.99  --inst_passive_queue_type               priority_queues
% 12.13/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.13/1.99  --inst_passive_queues_freq              [25;2]
% 12.13/1.99  --inst_dismatching                      true
% 12.13/1.99  --inst_eager_unprocessed_to_passive     true
% 12.13/1.99  --inst_prop_sim_given                   true
% 12.13/1.99  --inst_prop_sim_new                     false
% 12.13/1.99  --inst_subs_new                         false
% 12.13/1.99  --inst_eq_res_simp                      false
% 12.13/1.99  --inst_subs_given                       false
% 12.13/1.99  --inst_orphan_elimination               true
% 12.13/1.99  --inst_learning_loop_flag               true
% 12.13/1.99  --inst_learning_start                   3000
% 12.13/1.99  --inst_learning_factor                  2
% 12.13/1.99  --inst_start_prop_sim_after_learn       3
% 12.13/1.99  --inst_sel_renew                        solver
% 12.13/1.99  --inst_lit_activity_flag                true
% 12.13/1.99  --inst_restr_to_given                   false
% 12.13/1.99  --inst_activity_threshold               500
% 12.13/1.99  --inst_out_proof                        true
% 12.13/1.99  
% 12.13/1.99  ------ Resolution Options
% 12.13/1.99  
% 12.13/1.99  --resolution_flag                       false
% 12.13/1.99  --res_lit_sel                           adaptive
% 12.13/1.99  --res_lit_sel_side                      none
% 12.13/1.99  --res_ordering                          kbo
% 12.13/1.99  --res_to_prop_solver                    active
% 12.13/1.99  --res_prop_simpl_new                    false
% 12.13/1.99  --res_prop_simpl_given                  true
% 12.13/1.99  --res_passive_queue_type                priority_queues
% 12.13/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.13/1.99  --res_passive_queues_freq               [15;5]
% 12.13/1.99  --res_forward_subs                      full
% 12.13/1.99  --res_backward_subs                     full
% 12.13/1.99  --res_forward_subs_resolution           true
% 12.13/1.99  --res_backward_subs_resolution          true
% 12.13/1.99  --res_orphan_elimination                true
% 12.13/1.99  --res_time_limit                        2.
% 12.13/1.99  --res_out_proof                         true
% 12.13/1.99  
% 12.13/1.99  ------ Superposition Options
% 12.13/1.99  
% 12.13/1.99  --superposition_flag                    true
% 12.13/1.99  --sup_passive_queue_type                priority_queues
% 12.13/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.13/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.13/1.99  --demod_completeness_check              fast
% 12.13/1.99  --demod_use_ground                      true
% 12.13/1.99  --sup_to_prop_solver                    passive
% 12.13/1.99  --sup_prop_simpl_new                    true
% 12.13/1.99  --sup_prop_simpl_given                  true
% 12.13/1.99  --sup_fun_splitting                     false
% 12.13/1.99  --sup_smt_interval                      50000
% 12.13/1.99  
% 12.13/1.99  ------ Superposition Simplification Setup
% 12.13/1.99  
% 12.13/1.99  --sup_indices_passive                   []
% 12.13/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.13/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.13/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.99  --sup_full_bw                           [BwDemod]
% 12.13/1.99  --sup_immed_triv                        [TrivRules]
% 12.13/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.13/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.99  --sup_immed_bw_main                     []
% 12.13/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.13/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.13/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.13/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.13/1.99  
% 12.13/1.99  ------ Combination Options
% 12.13/1.99  
% 12.13/1.99  --comb_res_mult                         3
% 12.13/1.99  --comb_sup_mult                         2
% 12.13/1.99  --comb_inst_mult                        10
% 12.13/1.99  
% 12.13/1.99  ------ Debug Options
% 12.13/1.99  
% 12.13/1.99  --dbg_backtrace                         false
% 12.13/1.99  --dbg_dump_prop_clauses                 false
% 12.13/1.99  --dbg_dump_prop_clauses_file            -
% 12.13/1.99  --dbg_out_stat                          false
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  ------ Proving...
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  % SZS status Theorem for theBenchmark.p
% 12.13/1.99  
% 12.13/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 12.13/1.99  
% 12.13/1.99  fof(f4,axiom,(
% 12.13/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f40,plain,(
% 12.13/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.13/1.99    inference(cnf_transformation,[],[f4])).
% 12.13/1.99  
% 12.13/1.99  fof(f11,axiom,(
% 12.13/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f25,plain,(
% 12.13/1.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.13/1.99    inference(ennf_transformation,[],[f11])).
% 12.13/1.99  
% 12.13/1.99  fof(f26,plain,(
% 12.13/1.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.13/1.99    inference(flattening,[],[f25])).
% 12.13/1.99  
% 12.13/1.99  fof(f49,plain,(
% 12.13/1.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.13/1.99    inference(cnf_transformation,[],[f26])).
% 12.13/1.99  
% 12.13/1.99  fof(f12,conjecture,(
% 12.13/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f13,negated_conjecture,(
% 12.13/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 12.13/1.99    inference(negated_conjecture,[],[f12])).
% 12.13/1.99  
% 12.13/1.99  fof(f14,plain,(
% 12.13/1.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 12.13/1.99    inference(pure_predicate_removal,[],[f13])).
% 12.13/1.99  
% 12.13/1.99  fof(f27,plain,(
% 12.13/1.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 12.13/1.99    inference(ennf_transformation,[],[f14])).
% 12.13/1.99  
% 12.13/1.99  fof(f32,plain,(
% 12.13/1.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 12.13/1.99    introduced(choice_axiom,[])).
% 12.13/1.99  
% 12.13/1.99  fof(f31,plain,(
% 12.13/1.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 12.13/1.99    introduced(choice_axiom,[])).
% 12.13/1.99  
% 12.13/1.99  fof(f30,plain,(
% 12.13/1.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 12.13/1.99    introduced(choice_axiom,[])).
% 12.13/1.99  
% 12.13/1.99  fof(f33,plain,(
% 12.13/1.99    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 12.13/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32,f31,f30])).
% 12.13/1.99  
% 12.13/1.99  fof(f50,plain,(
% 12.13/1.99    l1_pre_topc(sK0)),
% 12.13/1.99    inference(cnf_transformation,[],[f33])).
% 12.13/1.99  
% 12.13/1.99  fof(f6,axiom,(
% 12.13/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f18,plain,(
% 12.13/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 12.13/1.99    inference(ennf_transformation,[],[f6])).
% 12.13/1.99  
% 12.13/1.99  fof(f19,plain,(
% 12.13/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 12.13/1.99    inference(flattening,[],[f18])).
% 12.13/1.99  
% 12.13/1.99  fof(f44,plain,(
% 12.13/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 12.13/1.99    inference(cnf_transformation,[],[f19])).
% 12.13/1.99  
% 12.13/1.99  fof(f51,plain,(
% 12.13/1.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.13/1.99    inference(cnf_transformation,[],[f33])).
% 12.13/1.99  
% 12.13/1.99  fof(f9,axiom,(
% 12.13/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f22,plain,(
% 12.13/1.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 12.13/1.99    inference(ennf_transformation,[],[f9])).
% 12.13/1.99  
% 12.13/1.99  fof(f23,plain,(
% 12.13/1.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 12.13/1.99    inference(flattening,[],[f22])).
% 12.13/1.99  
% 12.13/1.99  fof(f47,plain,(
% 12.13/1.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.13/1.99    inference(cnf_transformation,[],[f23])).
% 12.13/1.99  
% 12.13/1.99  fof(f8,axiom,(
% 12.13/1.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f21,plain,(
% 12.13/1.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.13/1.99    inference(ennf_transformation,[],[f8])).
% 12.13/1.99  
% 12.13/1.99  fof(f46,plain,(
% 12.13/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.13/1.99    inference(cnf_transformation,[],[f21])).
% 12.13/1.99  
% 12.13/1.99  fof(f53,plain,(
% 12.13/1.99    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 12.13/1.99    inference(cnf_transformation,[],[f33])).
% 12.13/1.99  
% 12.13/1.99  fof(f52,plain,(
% 12.13/1.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.13/1.99    inference(cnf_transformation,[],[f33])).
% 12.13/1.99  
% 12.13/1.99  fof(f10,axiom,(
% 12.13/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f24,plain,(
% 12.13/1.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.13/1.99    inference(ennf_transformation,[],[f10])).
% 12.13/1.99  
% 12.13/1.99  fof(f48,plain,(
% 12.13/1.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.13/1.99    inference(cnf_transformation,[],[f24])).
% 12.13/1.99  
% 12.13/1.99  fof(f3,axiom,(
% 12.13/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f16,plain,(
% 12.13/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 12.13/1.99    inference(ennf_transformation,[],[f3])).
% 12.13/1.99  
% 12.13/1.99  fof(f39,plain,(
% 12.13/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 12.13/1.99    inference(cnf_transformation,[],[f16])).
% 12.13/1.99  
% 12.13/1.99  fof(f7,axiom,(
% 12.13/1.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f20,plain,(
% 12.13/1.99    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.13/1.99    inference(ennf_transformation,[],[f7])).
% 12.13/1.99  
% 12.13/1.99  fof(f45,plain,(
% 12.13/1.99    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.13/1.99    inference(cnf_transformation,[],[f20])).
% 12.13/1.99  
% 12.13/1.99  fof(f2,axiom,(
% 12.13/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f15,plain,(
% 12.13/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 12.13/1.99    inference(ennf_transformation,[],[f2])).
% 12.13/1.99  
% 12.13/1.99  fof(f38,plain,(
% 12.13/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 12.13/1.99    inference(cnf_transformation,[],[f15])).
% 12.13/1.99  
% 12.13/1.99  fof(f5,axiom,(
% 12.13/1.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f17,plain,(
% 12.13/1.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 12.13/1.99    inference(ennf_transformation,[],[f5])).
% 12.13/1.99  
% 12.13/1.99  fof(f42,plain,(
% 12.13/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 12.13/1.99    inference(cnf_transformation,[],[f17])).
% 12.13/1.99  
% 12.13/1.99  fof(f1,axiom,(
% 12.13/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.13/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.13/1.99  
% 12.13/1.99  fof(f28,plain,(
% 12.13/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.13/1.99    inference(nnf_transformation,[],[f1])).
% 12.13/1.99  
% 12.13/1.99  fof(f29,plain,(
% 12.13/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.13/1.99    inference(flattening,[],[f28])).
% 12.13/1.99  
% 12.13/1.99  fof(f35,plain,(
% 12.13/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 12.13/1.99    inference(cnf_transformation,[],[f29])).
% 12.13/1.99  
% 12.13/1.99  fof(f54,plain,(
% 12.13/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.13/1.99    inference(equality_resolution,[],[f35])).
% 12.13/1.99  
% 12.13/1.99  fof(f36,plain,(
% 12.13/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 12.13/1.99    inference(cnf_transformation,[],[f29])).
% 12.13/1.99  
% 12.13/1.99  cnf(c_409,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.13/1.99      theory(equality) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1078,plain,
% 12.13/1.99      ( m1_subset_1(X0,X1)
% 12.13/1.99      | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | X0 != k7_subset_1(u1_struct_0(sK0),sK1,X2)
% 12.13/1.99      | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_409]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_9643,plain,
% 12.13/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | X0 != k7_subset_1(u1_struct_0(sK0),sK1,X1)
% 12.13/1.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_1078]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_25502,plain,
% 12.13/1.99      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | k4_xboole_0(sK1,X0) != k7_subset_1(u1_struct_0(sK0),sK1,X0)
% 12.13/1.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_9643]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_52078,plain,
% 12.13/1.99      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | k4_xboole_0(sK1,sK2) != k7_subset_1(u1_struct_0(sK0),sK1,sK2)
% 12.13/1.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_25502]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_6,plain,
% 12.13/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 12.13/1.99      inference(cnf_transformation,[],[f40]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1139,plain,
% 12.13/1.99      ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_43023,plain,
% 12.13/1.99      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_1139]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_15,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | ~ r1_tarski(X0,X2)
% 12.13/1.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 12.13/1.99      | ~ l1_pre_topc(X1) ),
% 12.13/1.99      inference(cnf_transformation,[],[f49]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_19,negated_conjecture,
% 12.13/1.99      ( l1_pre_topc(sK0) ),
% 12.13/1.99      inference(cnf_transformation,[],[f50]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_222,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | ~ r1_tarski(X0,X2)
% 12.13/1.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 12.13/1.99      | sK0 != X1 ),
% 12.13/1.99      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_223,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | ~ r1_tarski(X1,X0)
% 12.13/1.99      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 12.13/1.99      inference(unflattening,[status(thm)],[c_222]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_732,plain,
% 12.13/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.13/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.13/1.99      | r1_tarski(X1,X0) != iProver_top
% 12.13/1.99      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_10,plain,
% 12.13/1.99      ( ~ r1_xboole_0(X0,X1)
% 12.13/1.99      | ~ r1_tarski(X0,X2)
% 12.13/1.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 12.13/1.99      inference(cnf_transformation,[],[f44]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_738,plain,
% 12.13/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 12.13/1.99      | r1_tarski(X0,X2) != iProver_top
% 12.13/1.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) = iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_18,negated_conjecture,
% 12.13/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 12.13/1.99      inference(cnf_transformation,[],[f51]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_733,plain,
% 12.13/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_13,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | ~ l1_pre_topc(X1) ),
% 12.13/1.99      inference(cnf_transformation,[],[f47]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_252,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | sK0 != X1 ),
% 12.13/1.99      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_253,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 12.13/1.99      inference(unflattening,[status(thm)],[c_252]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_730,plain,
% 12.13/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.13/1.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_12,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.13/1.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 12.13/1.99      inference(cnf_transformation,[],[f46]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_736,plain,
% 12.13/1.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 12.13/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3097,plain,
% 12.13/1.99      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),X1) = k4_xboole_0(k1_tops_1(sK0,X0),X1)
% 12.13/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_730,c_736]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_7882,plain,
% 12.13/1.99      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_733,c_3097]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3096,plain,
% 12.13/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_733,c_736]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_16,negated_conjecture,
% 12.13/1.99      ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 12.13/1.99      inference(cnf_transformation,[],[f53]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_735,plain,
% 12.13/1.99      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3270,plain,
% 12.13/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_3096,c_735]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_8034,plain,
% 12.13/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 12.13/1.99      inference(demodulation,[status(thm)],[c_7882,c_3270]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_8055,plain,
% 12.13/1.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top
% 12.13/1.99      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_738,c_8034]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_17,negated_conjecture,
% 12.13/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 12.13/1.99      inference(cnf_transformation,[],[f52]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_734,plain,
% 12.13/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_14,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 12.13/1.99      | ~ l1_pre_topc(X1) ),
% 12.13/1.99      inference(cnf_transformation,[],[f48]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_240,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.13/1.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 12.13/1.99      | sK0 != X1 ),
% 12.13/1.99      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_241,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 12.13/1.99      inference(unflattening,[status(thm)],[c_240]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_731,plain,
% 12.13/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.13/1.99      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_960,plain,
% 12.13/1.99      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_734,c_731]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_5,plain,
% 12.13/1.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 12.13/1.99      inference(cnf_transformation,[],[f39]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_743,plain,
% 12.13/1.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1420,plain,
% 12.13/1.99      ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_960,c_743]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_11,plain,
% 12.13/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.13/1.99      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 12.13/1.99      inference(cnf_transformation,[],[f45]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_737,plain,
% 12.13/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 12.13/1.99      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3272,plain,
% 12.13/1.99      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 12.13/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_3096,c_737]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_21,plain,
% 12.13/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_5349,plain,
% 12.13/1.99      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 12.13/1.99      inference(global_propositional_subsumption,
% 12.13/1.99                [status(thm)],
% 12.13/1.99                [c_3272,c_21]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_5360,plain,
% 12.13/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) = iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_5349,c_731]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3,plain,
% 12.13/1.99      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 12.13/1.99      inference(cnf_transformation,[],[f38]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_745,plain,
% 12.13/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 12.13/1.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_6262,plain,
% 12.13/1.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X0) = iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_5360,c_745]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_8,plain,
% 12.13/1.99      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.13/1.99      inference(cnf_transformation,[],[f42]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_740,plain,
% 12.13/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 12.13/1.99      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) != iProver_top ),
% 12.13/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_8811,plain,
% 12.13/1.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,k2_xboole_0(X0,X1))),X0) = iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_6262,c_740]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_12059,plain,
% 12.13/1.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) = iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_1420,c_8811]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_39249,plain,
% 12.13/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
% 12.13/1.99      inference(global_propositional_subsumption,
% 12.13/1.99                [status(thm)],
% 12.13/1.99                [c_8055,c_12059]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_39254,plain,
% 12.13/1.99      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.13/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.13/1.99      | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top ),
% 12.13/1.99      inference(superposition,[status(thm)],[c_732,c_39249]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_39255,plain,
% 12.13/1.99      ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 12.13/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_39254]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_1,plain,
% 12.13/1.99      ( r1_tarski(X0,X0) ),
% 12.13/1.99      inference(cnf_transformation,[],[f54]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_886,plain,
% 12.13/1.99      ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_34949,plain,
% 12.13/1.99      ( r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_886]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_0,plain,
% 12.13/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 12.13/1.99      inference(cnf_transformation,[],[f36]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_2491,plain,
% 12.13/1.99      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
% 12.13/1.99      | ~ r1_tarski(k4_xboole_0(X1,X2),X0)
% 12.13/1.99      | k4_xboole_0(X1,X2) = X0 ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_7776,plain,
% 12.13/1.99      ( ~ r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))
% 12.13/1.99      | ~ r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))
% 12.13/1.99      | k4_xboole_0(X2,X1) = k4_xboole_0(X0,X1) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_2491]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_21550,plain,
% 12.13/1.99      ( ~ r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,sK2))
% 12.13/1.99      | ~ r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK2))
% 12.13/1.99      | k4_xboole_0(X0,sK2) = k4_xboole_0(sK1,sK2) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_7776]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_34948,plain,
% 12.13/1.99      ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
% 12.13/1.99      | k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_21550]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_404,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_2501,plain,
% 12.13/1.99      ( X0 != X1 | k4_xboole_0(X2,X3) != X1 | k4_xboole_0(X2,X3) = X0 ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_404]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_6083,plain,
% 12.13/1.99      ( X0 != k4_xboole_0(X1,X2)
% 12.13/1.99      | k4_xboole_0(X1,X2) = X0
% 12.13/1.99      | k4_xboole_0(X1,X2) != k4_xboole_0(X1,X2) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_2501]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_12244,plain,
% 12.13/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) != k4_xboole_0(sK1,X0)
% 12.13/1.99      | k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
% 12.13/1.99      | k4_xboole_0(sK1,X0) != k4_xboole_0(sK1,X0) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_6083]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_32561,plain,
% 12.13/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
% 12.13/1.99      | k4_xboole_0(sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,sK2)
% 12.13/1.99      | k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_12244]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_920,plain,
% 12.13/1.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_10076,plain,
% 12.13/1.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_920]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_403,plain,( X0 = X0 ),theory(equality) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3227,plain,
% 12.13/1.99      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_403]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_930,plain,
% 12.13/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(c_3219,plain,
% 12.13/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.13/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 12.13/1.99      inference(instantiation,[status(thm)],[c_930]) ).
% 12.13/1.99  
% 12.13/1.99  cnf(contradiction,plain,
% 12.13/1.99      ( $false ),
% 12.13/1.99      inference(minisat,
% 12.13/1.99                [status(thm)],
% 12.13/1.99                [c_52078,c_43023,c_39255,c_34949,c_34948,c_32561,c_10076,
% 12.13/1.99                 c_3227,c_3219,c_18]) ).
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.13/1.99  
% 12.13/1.99  ------                               Statistics
% 12.13/1.99  
% 12.13/1.99  ------ General
% 12.13/1.99  
% 12.13/1.99  abstr_ref_over_cycles:                  0
% 12.13/1.99  abstr_ref_under_cycles:                 0
% 12.13/1.99  gc_basic_clause_elim:                   0
% 12.13/1.99  forced_gc_time:                         0
% 12.13/1.99  parsing_time:                           0.009
% 12.13/1.99  unif_index_cands_time:                  0.
% 12.13/1.99  unif_index_add_time:                    0.
% 12.13/1.99  orderings_time:                         0.
% 12.13/1.99  out_proof_time:                         0.016
% 12.13/1.99  total_time:                             1.446
% 12.13/1.99  num_of_symbols:                         44
% 12.13/1.99  num_of_terms:                           68090
% 12.13/1.99  
% 12.13/1.99  ------ Preprocessing
% 12.13/1.99  
% 12.13/1.99  num_of_splits:                          0
% 12.13/1.99  num_of_split_atoms:                     0
% 12.13/1.99  num_of_reused_defs:                     0
% 12.13/1.99  num_eq_ax_congr_red:                    15
% 12.13/1.99  num_of_sem_filtered_clauses:            1
% 12.13/1.99  num_of_subtypes:                        0
% 12.13/1.99  monotx_restored_types:                  0
% 12.13/1.99  sat_num_of_epr_types:                   0
% 12.13/1.99  sat_num_of_non_cyclic_types:            0
% 12.13/1.99  sat_guarded_non_collapsed_types:        0
% 12.13/1.99  num_pure_diseq_elim:                    0
% 12.13/1.99  simp_replaced_by:                       0
% 12.13/1.99  res_preprocessed:                       92
% 12.13/1.99  prep_upred:                             0
% 12.13/1.99  prep_unflattend:                        3
% 12.13/1.99  smt_new_axioms:                         0
% 12.13/1.99  pred_elim_cands:                        3
% 12.13/1.99  pred_elim:                              1
% 12.13/1.99  pred_elim_cl:                           1
% 12.13/1.99  pred_elim_cycles:                       3
% 12.13/1.99  merged_defs:                            0
% 12.13/1.99  merged_defs_ncl:                        0
% 12.13/1.99  bin_hyper_res:                          0
% 12.13/1.99  prep_cycles:                            4
% 12.13/1.99  pred_elim_time:                         0.001
% 12.13/1.99  splitting_time:                         0.
% 12.13/1.99  sem_filter_time:                        0.
% 12.13/1.99  monotx_time:                            0.
% 12.13/1.99  subtype_inf_time:                       0.
% 12.13/1.99  
% 12.13/1.99  ------ Problem properties
% 12.13/1.99  
% 12.13/1.99  clauses:                                18
% 12.13/1.99  conjectures:                            3
% 12.13/1.99  epr:                                    2
% 12.13/1.99  horn:                                   18
% 12.13/1.99  ground:                                 3
% 12.13/1.99  unary:                                  5
% 12.13/1.99  binary:                                 9
% 12.13/1.99  lits:                                   36
% 12.13/1.99  lits_eq:                                3
% 12.13/1.99  fd_pure:                                0
% 12.13/1.99  fd_pseudo:                              0
% 12.13/1.99  fd_cond:                                0
% 12.13/1.99  fd_pseudo_cond:                         1
% 12.13/1.99  ac_symbols:                             0
% 12.13/1.99  
% 12.13/1.99  ------ Propositional Solver
% 12.13/1.99  
% 12.13/1.99  prop_solver_calls:                      31
% 12.13/1.99  prop_fast_solver_calls:                 1040
% 12.13/1.99  smt_solver_calls:                       0
% 12.13/1.99  smt_fast_solver_calls:                  0
% 12.13/1.99  prop_num_of_clauses:                    25236
% 12.13/1.99  prop_preprocess_simplified:             38679
% 12.13/1.99  prop_fo_subsumed:                       15
% 12.13/1.99  prop_solver_time:                       0.
% 12.13/1.99  smt_solver_time:                        0.
% 12.13/1.99  smt_fast_solver_time:                   0.
% 12.13/1.99  prop_fast_solver_time:                  0.
% 12.13/1.99  prop_unsat_core_time:                   0.003
% 12.13/1.99  
% 12.13/1.99  ------ QBF
% 12.13/1.99  
% 12.13/1.99  qbf_q_res:                              0
% 12.13/1.99  qbf_num_tautologies:                    0
% 12.13/1.99  qbf_prep_cycles:                        0
% 12.13/1.99  
% 12.13/1.99  ------ BMC1
% 12.13/1.99  
% 12.13/1.99  bmc1_current_bound:                     -1
% 12.13/1.99  bmc1_last_solved_bound:                 -1
% 12.13/1.99  bmc1_unsat_core_size:                   -1
% 12.13/1.99  bmc1_unsat_core_parents_size:           -1
% 12.13/1.99  bmc1_merge_next_fun:                    0
% 12.13/1.99  bmc1_unsat_core_clauses_time:           0.
% 12.13/1.99  
% 12.13/1.99  ------ Instantiation
% 12.13/1.99  
% 12.13/1.99  inst_num_of_clauses:                    5317
% 12.13/1.99  inst_num_in_passive:                    2002
% 12.13/1.99  inst_num_in_active:                     2343
% 12.13/1.99  inst_num_in_unprocessed:                971
% 12.13/1.99  inst_num_of_loops:                      2411
% 12.13/1.99  inst_num_of_learning_restarts:          0
% 12.13/1.99  inst_num_moves_active_passive:          65
% 12.13/1.99  inst_lit_activity:                      0
% 12.13/1.99  inst_lit_activity_moves:                1
% 12.13/1.99  inst_num_tautologies:                   0
% 12.13/1.99  inst_num_prop_implied:                  0
% 12.13/1.99  inst_num_existing_simplified:           0
% 12.13/1.99  inst_num_eq_res_simplified:             0
% 12.13/1.99  inst_num_child_elim:                    0
% 12.13/1.99  inst_num_of_dismatching_blockings:      3462
% 12.13/1.99  inst_num_of_non_proper_insts:           6902
% 12.13/1.99  inst_num_of_duplicates:                 0
% 12.13/1.99  inst_inst_num_from_inst_to_res:         0
% 12.13/1.99  inst_dismatching_checking_time:         0.
% 12.13/1.99  
% 12.13/1.99  ------ Resolution
% 12.13/1.99  
% 12.13/1.99  res_num_of_clauses:                     0
% 12.13/1.99  res_num_in_passive:                     0
% 12.13/1.99  res_num_in_active:                      0
% 12.13/1.99  res_num_of_loops:                       96
% 12.13/1.99  res_forward_subset_subsumed:            367
% 12.13/1.99  res_backward_subset_subsumed:           0
% 12.13/1.99  res_forward_subsumed:                   0
% 12.13/1.99  res_backward_subsumed:                  0
% 12.13/1.99  res_forward_subsumption_resolution:     0
% 12.13/1.99  res_backward_subsumption_resolution:    0
% 12.13/1.99  res_clause_to_clause_subsumption:       24091
% 12.13/1.99  res_orphan_elimination:                 0
% 12.13/1.99  res_tautology_del:                      150
% 12.13/1.99  res_num_eq_res_simplified:              0
% 12.13/1.99  res_num_sel_changes:                    0
% 12.13/1.99  res_moves_from_active_to_pass:          0
% 12.13/1.99  
% 12.13/1.99  ------ Superposition
% 12.13/1.99  
% 12.13/1.99  sup_time_total:                         0.
% 12.13/1.99  sup_time_generating:                    0.
% 12.13/1.99  sup_time_sim_full:                      0.
% 12.13/1.99  sup_time_sim_immed:                     0.
% 12.13/1.99  
% 12.13/1.99  sup_num_of_clauses:                     1986
% 12.13/1.99  sup_num_in_active:                      480
% 12.13/1.99  sup_num_in_passive:                     1506
% 12.13/1.99  sup_num_of_loops:                       482
% 12.13/1.99  sup_fw_superposition:                   3612
% 12.13/1.99  sup_bw_superposition:                   1483
% 12.13/1.99  sup_immediate_simplified:               511
% 12.13/1.99  sup_given_eliminated:                   0
% 12.13/1.99  comparisons_done:                       0
% 12.13/1.99  comparisons_avoided:                    0
% 12.13/1.99  
% 12.13/1.99  ------ Simplifications
% 12.13/1.99  
% 12.13/1.99  
% 12.13/1.99  sim_fw_subset_subsumed:                 2
% 12.13/1.99  sim_bw_subset_subsumed:                 0
% 12.13/1.99  sim_fw_subsumed:                        437
% 12.13/1.99  sim_bw_subsumed:                        0
% 12.13/1.99  sim_fw_subsumption_res:                 0
% 12.13/1.99  sim_bw_subsumption_res:                 0
% 12.13/1.99  sim_tautology_del:                      36
% 12.13/1.99  sim_eq_tautology_del:                   7
% 12.13/1.99  sim_eq_res_simp:                        0
% 12.13/1.99  sim_fw_demodulated:                     2
% 12.13/1.99  sim_bw_demodulated:                     3
% 12.13/1.99  sim_light_normalised:                   74
% 12.13/1.99  sim_joinable_taut:                      0
% 12.13/1.99  sim_joinable_simp:                      0
% 12.13/1.99  sim_ac_normalised:                      0
% 12.13/1.99  sim_smt_subsumption:                    0
% 12.13/1.99  
%------------------------------------------------------------------------------
