%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:51 EST 2020

% Result     : Theorem 36.06s
% Output     : CNFRefutation 36.06s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 333 expanded)
%              Number of clauses        :   94 ( 151 expanded)
%              Number of leaves         :   17 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  391 (1040 expanded)
%              Number of equality atoms :   86 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28,f27,f26])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_70064,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != X1 ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_70236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_70064])).

cnf(c_70430,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1)
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_70236])).

cnf(c_126220,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_70430])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_118,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_118])).

cnf(c_144,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_119])).

cnf(c_289,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_314,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_144,c_290])).

cnf(c_70761,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_87591,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),X0),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_70761])).

cnf(c_98463,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_87591])).

cnf(c_373,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_70388,plain,
    ( X0 != X1
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_70888,plain,
    ( X0 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_70388])).

cnf(c_72018,plain,
    ( k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_70888])).

cnf(c_98257,plain,
    ( k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_72018])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_145,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_119])).

cnf(c_315,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_145,c_290])).

cnf(c_74098,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_79571,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
    | k4_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_74098])).

cnf(c_92074,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_79571])).

cnf(c_374,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_70270,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_70557,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_70270])).

cnf(c_71286,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(X0,X1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,X1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_70557])).

cnf(c_75964,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(X0,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_71286])).

cnf(c_89091,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_75964])).

cnf(c_70286,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_70568,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_70286])).

cnf(c_71301,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(X0,X1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,X1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_70568])).

cnf(c_73531,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,X0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,X0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_71301])).

cnf(c_77202,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_73531])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_70069,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_70218,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_70069])).

cnf(c_70215,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_70069])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5503,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_25757,plain,
    ( r1_tarski(sK2,k2_xboole_0(X0,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5503])).

cnf(c_59480,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_25757])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8905,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_47143,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8905])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_832,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1405,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_2267,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_941,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_1399,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_2251,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_1394,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_2243,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_699,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_701,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1411,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_701])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_698,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1412,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_701])).

cnf(c_694,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1571,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_694])).

cnf(c_1749,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1411,c_1571])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1106,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1532,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_1097,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1522,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1315,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_372,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1161,plain,
    ( k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) = k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_824,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1144,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_1141,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1040,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1028,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_743,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_740,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_727,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_126220,c_98463,c_98257,c_92074,c_89091,c_77202,c_70218,c_70215,c_59480,c_47143,c_2267,c_2251,c_2243,c_1749,c_1532,c_1522,c_1315,c_1161,c_1144,c_1141,c_1040,c_1028,c_743,c_740,c_727,c_12,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 36.06/5.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.06/5.06  
% 36.06/5.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 36.06/5.06  
% 36.06/5.06  ------  iProver source info
% 36.06/5.06  
% 36.06/5.06  git: date: 2020-06-30 10:37:57 +0100
% 36.06/5.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 36.06/5.06  git: non_committed_changes: false
% 36.06/5.06  git: last_make_outside_of_git: false
% 36.06/5.06  
% 36.06/5.06  ------ 
% 36.06/5.06  
% 36.06/5.06  ------ Input Options
% 36.06/5.06  
% 36.06/5.06  --out_options                           all
% 36.06/5.06  --tptp_safe_out                         true
% 36.06/5.06  --problem_path                          ""
% 36.06/5.06  --include_path                          ""
% 36.06/5.06  --clausifier                            res/vclausify_rel
% 36.06/5.06  --clausifier_options                    ""
% 36.06/5.06  --stdin                                 false
% 36.06/5.06  --stats_out                             all
% 36.06/5.06  
% 36.06/5.06  ------ General Options
% 36.06/5.06  
% 36.06/5.06  --fof                                   false
% 36.06/5.06  --time_out_real                         305.
% 36.06/5.06  --time_out_virtual                      -1.
% 36.06/5.06  --symbol_type_check                     false
% 36.06/5.06  --clausify_out                          false
% 36.06/5.06  --sig_cnt_out                           false
% 36.06/5.06  --trig_cnt_out                          false
% 36.06/5.06  --trig_cnt_out_tolerance                1.
% 36.06/5.06  --trig_cnt_out_sk_spl                   false
% 36.06/5.06  --abstr_cl_out                          false
% 36.06/5.06  
% 36.06/5.06  ------ Global Options
% 36.06/5.06  
% 36.06/5.06  --schedule                              default
% 36.06/5.06  --add_important_lit                     false
% 36.06/5.06  --prop_solver_per_cl                    1000
% 36.06/5.06  --min_unsat_core                        false
% 36.06/5.06  --soft_assumptions                      false
% 36.06/5.06  --soft_lemma_size                       3
% 36.06/5.06  --prop_impl_unit_size                   0
% 36.06/5.06  --prop_impl_unit                        []
% 36.06/5.06  --share_sel_clauses                     true
% 36.06/5.06  --reset_solvers                         false
% 36.06/5.06  --bc_imp_inh                            [conj_cone]
% 36.06/5.06  --conj_cone_tolerance                   3.
% 36.06/5.06  --extra_neg_conj                        none
% 36.06/5.06  --large_theory_mode                     true
% 36.06/5.06  --prolific_symb_bound                   200
% 36.06/5.06  --lt_threshold                          2000
% 36.06/5.06  --clause_weak_htbl                      true
% 36.06/5.06  --gc_record_bc_elim                     false
% 36.06/5.06  
% 36.06/5.06  ------ Preprocessing Options
% 36.06/5.06  
% 36.06/5.06  --preprocessing_flag                    true
% 36.06/5.06  --time_out_prep_mult                    0.1
% 36.06/5.06  --splitting_mode                        input
% 36.06/5.06  --splitting_grd                         true
% 36.06/5.06  --splitting_cvd                         false
% 36.06/5.06  --splitting_cvd_svl                     false
% 36.06/5.06  --splitting_nvd                         32
% 36.06/5.06  --sub_typing                            true
% 36.06/5.06  --prep_gs_sim                           true
% 36.06/5.06  --prep_unflatten                        true
% 36.06/5.06  --prep_res_sim                          true
% 36.06/5.06  --prep_upred                            true
% 36.06/5.06  --prep_sem_filter                       exhaustive
% 36.06/5.06  --prep_sem_filter_out                   false
% 36.06/5.06  --pred_elim                             true
% 36.06/5.06  --res_sim_input                         true
% 36.06/5.06  --eq_ax_congr_red                       true
% 36.06/5.06  --pure_diseq_elim                       true
% 36.06/5.06  --brand_transform                       false
% 36.06/5.06  --non_eq_to_eq                          false
% 36.06/5.06  --prep_def_merge                        true
% 36.06/5.06  --prep_def_merge_prop_impl              false
% 36.06/5.06  --prep_def_merge_mbd                    true
% 36.06/5.06  --prep_def_merge_tr_red                 false
% 36.06/5.06  --prep_def_merge_tr_cl                  false
% 36.06/5.06  --smt_preprocessing                     true
% 36.06/5.06  --smt_ac_axioms                         fast
% 36.06/5.06  --preprocessed_out                      false
% 36.06/5.06  --preprocessed_stats                    false
% 36.06/5.06  
% 36.06/5.06  ------ Abstraction refinement Options
% 36.06/5.06  
% 36.06/5.06  --abstr_ref                             []
% 36.06/5.06  --abstr_ref_prep                        false
% 36.06/5.06  --abstr_ref_until_sat                   false
% 36.06/5.06  --abstr_ref_sig_restrict                funpre
% 36.06/5.06  --abstr_ref_af_restrict_to_split_sk     false
% 36.06/5.06  --abstr_ref_under                       []
% 36.06/5.06  
% 36.06/5.06  ------ SAT Options
% 36.06/5.06  
% 36.06/5.06  --sat_mode                              false
% 36.06/5.06  --sat_fm_restart_options                ""
% 36.06/5.06  --sat_gr_def                            false
% 36.06/5.06  --sat_epr_types                         true
% 36.06/5.06  --sat_non_cyclic_types                  false
% 36.06/5.06  --sat_finite_models                     false
% 36.06/5.06  --sat_fm_lemmas                         false
% 36.06/5.06  --sat_fm_prep                           false
% 36.06/5.06  --sat_fm_uc_incr                        true
% 36.06/5.06  --sat_out_model                         small
% 36.06/5.06  --sat_out_clauses                       false
% 36.06/5.06  
% 36.06/5.06  ------ QBF Options
% 36.06/5.06  
% 36.06/5.06  --qbf_mode                              false
% 36.06/5.06  --qbf_elim_univ                         false
% 36.06/5.06  --qbf_dom_inst                          none
% 36.06/5.06  --qbf_dom_pre_inst                      false
% 36.06/5.06  --qbf_sk_in                             false
% 36.06/5.06  --qbf_pred_elim                         true
% 36.06/5.06  --qbf_split                             512
% 36.06/5.06  
% 36.06/5.06  ------ BMC1 Options
% 36.06/5.06  
% 36.06/5.06  --bmc1_incremental                      false
% 36.06/5.06  --bmc1_axioms                           reachable_all
% 36.06/5.06  --bmc1_min_bound                        0
% 36.06/5.06  --bmc1_max_bound                        -1
% 36.06/5.06  --bmc1_max_bound_default                -1
% 36.06/5.06  --bmc1_symbol_reachability              true
% 36.06/5.06  --bmc1_property_lemmas                  false
% 36.06/5.06  --bmc1_k_induction                      false
% 36.06/5.06  --bmc1_non_equiv_states                 false
% 36.06/5.06  --bmc1_deadlock                         false
% 36.06/5.06  --bmc1_ucm                              false
% 36.06/5.06  --bmc1_add_unsat_core                   none
% 36.06/5.06  --bmc1_unsat_core_children              false
% 36.06/5.06  --bmc1_unsat_core_extrapolate_axioms    false
% 36.06/5.06  --bmc1_out_stat                         full
% 36.06/5.06  --bmc1_ground_init                      false
% 36.06/5.06  --bmc1_pre_inst_next_state              false
% 36.06/5.06  --bmc1_pre_inst_state                   false
% 36.06/5.06  --bmc1_pre_inst_reach_state             false
% 36.06/5.06  --bmc1_out_unsat_core                   false
% 36.06/5.06  --bmc1_aig_witness_out                  false
% 36.06/5.06  --bmc1_verbose                          false
% 36.06/5.06  --bmc1_dump_clauses_tptp                false
% 36.06/5.06  --bmc1_dump_unsat_core_tptp             false
% 36.06/5.06  --bmc1_dump_file                        -
% 36.06/5.06  --bmc1_ucm_expand_uc_limit              128
% 36.06/5.06  --bmc1_ucm_n_expand_iterations          6
% 36.06/5.06  --bmc1_ucm_extend_mode                  1
% 36.06/5.06  --bmc1_ucm_init_mode                    2
% 36.06/5.06  --bmc1_ucm_cone_mode                    none
% 36.06/5.06  --bmc1_ucm_reduced_relation_type        0
% 36.06/5.06  --bmc1_ucm_relax_model                  4
% 36.06/5.06  --bmc1_ucm_full_tr_after_sat            true
% 36.06/5.06  --bmc1_ucm_expand_neg_assumptions       false
% 36.06/5.06  --bmc1_ucm_layered_model                none
% 36.06/5.06  --bmc1_ucm_max_lemma_size               10
% 36.06/5.06  
% 36.06/5.06  ------ AIG Options
% 36.06/5.06  
% 36.06/5.06  --aig_mode                              false
% 36.06/5.06  
% 36.06/5.06  ------ Instantiation Options
% 36.06/5.06  
% 36.06/5.06  --instantiation_flag                    true
% 36.06/5.06  --inst_sos_flag                         true
% 36.06/5.06  --inst_sos_phase                        true
% 36.06/5.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 36.06/5.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 36.06/5.06  --inst_lit_sel_side                     num_symb
% 36.06/5.06  --inst_solver_per_active                1400
% 36.06/5.06  --inst_solver_calls_frac                1.
% 36.06/5.06  --inst_passive_queue_type               priority_queues
% 36.06/5.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 36.06/5.06  --inst_passive_queues_freq              [25;2]
% 36.06/5.06  --inst_dismatching                      true
% 36.06/5.06  --inst_eager_unprocessed_to_passive     true
% 36.06/5.06  --inst_prop_sim_given                   true
% 36.06/5.06  --inst_prop_sim_new                     false
% 36.06/5.06  --inst_subs_new                         false
% 36.06/5.06  --inst_eq_res_simp                      false
% 36.06/5.06  --inst_subs_given                       false
% 36.06/5.06  --inst_orphan_elimination               true
% 36.06/5.06  --inst_learning_loop_flag               true
% 36.06/5.06  --inst_learning_start                   3000
% 36.06/5.06  --inst_learning_factor                  2
% 36.06/5.06  --inst_start_prop_sim_after_learn       3
% 36.06/5.06  --inst_sel_renew                        solver
% 36.06/5.06  --inst_lit_activity_flag                true
% 36.06/5.06  --inst_restr_to_given                   false
% 36.06/5.06  --inst_activity_threshold               500
% 36.06/5.06  --inst_out_proof                        true
% 36.06/5.06  
% 36.06/5.06  ------ Resolution Options
% 36.06/5.06  
% 36.06/5.06  --resolution_flag                       true
% 36.06/5.06  --res_lit_sel                           adaptive
% 36.06/5.06  --res_lit_sel_side                      none
% 36.06/5.06  --res_ordering                          kbo
% 36.06/5.06  --res_to_prop_solver                    active
% 36.06/5.06  --res_prop_simpl_new                    false
% 36.06/5.06  --res_prop_simpl_given                  true
% 36.06/5.06  --res_passive_queue_type                priority_queues
% 36.06/5.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 36.06/5.06  --res_passive_queues_freq               [15;5]
% 36.06/5.06  --res_forward_subs                      full
% 36.06/5.06  --res_backward_subs                     full
% 36.06/5.06  --res_forward_subs_resolution           true
% 36.06/5.06  --res_backward_subs_resolution          true
% 36.06/5.06  --res_orphan_elimination                true
% 36.06/5.06  --res_time_limit                        2.
% 36.06/5.06  --res_out_proof                         true
% 36.06/5.06  
% 36.06/5.06  ------ Superposition Options
% 36.06/5.06  
% 36.06/5.06  --superposition_flag                    true
% 36.06/5.06  --sup_passive_queue_type                priority_queues
% 36.06/5.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 36.06/5.06  --sup_passive_queues_freq               [8;1;4]
% 36.06/5.06  --demod_completeness_check              fast
% 36.06/5.06  --demod_use_ground                      true
% 36.06/5.06  --sup_to_prop_solver                    passive
% 36.06/5.06  --sup_prop_simpl_new                    true
% 36.06/5.06  --sup_prop_simpl_given                  true
% 36.06/5.06  --sup_fun_splitting                     true
% 36.06/5.06  --sup_smt_interval                      50000
% 36.06/5.06  
% 36.06/5.06  ------ Superposition Simplification Setup
% 36.06/5.06  
% 36.06/5.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 36.06/5.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 36.06/5.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 36.06/5.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 36.06/5.06  --sup_full_triv                         [TrivRules;PropSubs]
% 36.06/5.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 36.06/5.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 36.06/5.06  --sup_immed_triv                        [TrivRules]
% 36.06/5.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 36.06/5.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 36.06/5.06  --sup_immed_bw_main                     []
% 36.06/5.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 36.06/5.06  --sup_input_triv                        [Unflattening;TrivRules]
% 36.06/5.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 36.06/5.06  --sup_input_bw                          []
% 36.06/5.06  
% 36.06/5.06  ------ Combination Options
% 36.06/5.06  
% 36.06/5.06  --comb_res_mult                         3
% 36.06/5.06  --comb_sup_mult                         2
% 36.06/5.06  --comb_inst_mult                        10
% 36.06/5.06  
% 36.06/5.06  ------ Debug Options
% 36.06/5.06  
% 36.06/5.06  --dbg_backtrace                         false
% 36.06/5.06  --dbg_dump_prop_clauses                 false
% 36.06/5.06  --dbg_dump_prop_clauses_file            -
% 36.06/5.06  --dbg_out_stat                          false
% 36.06/5.06  ------ Parsing...
% 36.06/5.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 36.06/5.06  
% 36.06/5.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 36.06/5.06  
% 36.06/5.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 36.06/5.06  
% 36.06/5.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 36.06/5.06  ------ Proving...
% 36.06/5.06  ------ Problem Properties 
% 36.06/5.06  
% 36.06/5.06  
% 36.06/5.06  clauses                                 14
% 36.06/5.06  conjectures                             3
% 36.06/5.06  EPR                                     3
% 36.06/5.06  Horn                                    14
% 36.06/5.06  unary                                   5
% 36.06/5.06  binary                                  4
% 36.06/5.06  lits                                    29
% 36.06/5.06  lits eq                                 2
% 36.06/5.06  fd_pure                                 0
% 36.06/5.06  fd_pseudo                               0
% 36.06/5.06  fd_cond                                 0
% 36.06/5.06  fd_pseudo_cond                          1
% 36.06/5.06  AC symbols                              0
% 36.06/5.06  
% 36.06/5.06  ------ Schedule dynamic 5 is on 
% 36.06/5.06  
% 36.06/5.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 36.06/5.06  
% 36.06/5.06  
% 36.06/5.06  ------ 
% 36.06/5.06  Current options:
% 36.06/5.06  ------ 
% 36.06/5.06  
% 36.06/5.06  ------ Input Options
% 36.06/5.06  
% 36.06/5.06  --out_options                           all
% 36.06/5.06  --tptp_safe_out                         true
% 36.06/5.06  --problem_path                          ""
% 36.06/5.06  --include_path                          ""
% 36.06/5.06  --clausifier                            res/vclausify_rel
% 36.06/5.06  --clausifier_options                    ""
% 36.06/5.06  --stdin                                 false
% 36.06/5.06  --stats_out                             all
% 36.06/5.06  
% 36.06/5.06  ------ General Options
% 36.06/5.06  
% 36.06/5.06  --fof                                   false
% 36.06/5.06  --time_out_real                         305.
% 36.06/5.06  --time_out_virtual                      -1.
% 36.06/5.06  --symbol_type_check                     false
% 36.06/5.06  --clausify_out                          false
% 36.06/5.06  --sig_cnt_out                           false
% 36.06/5.06  --trig_cnt_out                          false
% 36.06/5.06  --trig_cnt_out_tolerance                1.
% 36.06/5.06  --trig_cnt_out_sk_spl                   false
% 36.06/5.06  --abstr_cl_out                          false
% 36.06/5.06  
% 36.06/5.06  ------ Global Options
% 36.06/5.06  
% 36.06/5.06  --schedule                              default
% 36.06/5.06  --add_important_lit                     false
% 36.06/5.06  --prop_solver_per_cl                    1000
% 36.06/5.06  --min_unsat_core                        false
% 36.06/5.06  --soft_assumptions                      false
% 36.06/5.06  --soft_lemma_size                       3
% 36.06/5.06  --prop_impl_unit_size                   0
% 36.06/5.06  --prop_impl_unit                        []
% 36.06/5.06  --share_sel_clauses                     true
% 36.06/5.06  --reset_solvers                         false
% 36.06/5.06  --bc_imp_inh                            [conj_cone]
% 36.06/5.06  --conj_cone_tolerance                   3.
% 36.06/5.06  --extra_neg_conj                        none
% 36.06/5.06  --large_theory_mode                     true
% 36.06/5.06  --prolific_symb_bound                   200
% 36.06/5.06  --lt_threshold                          2000
% 36.06/5.06  --clause_weak_htbl                      true
% 36.06/5.06  --gc_record_bc_elim                     false
% 36.06/5.06  
% 36.06/5.06  ------ Preprocessing Options
% 36.06/5.06  
% 36.06/5.06  --preprocessing_flag                    true
% 36.06/5.06  --time_out_prep_mult                    0.1
% 36.06/5.06  --splitting_mode                        input
% 36.06/5.06  --splitting_grd                         true
% 36.06/5.06  --splitting_cvd                         false
% 36.06/5.06  --splitting_cvd_svl                     false
% 36.06/5.06  --splitting_nvd                         32
% 36.06/5.06  --sub_typing                            true
% 36.06/5.06  --prep_gs_sim                           true
% 36.06/5.06  --prep_unflatten                        true
% 36.06/5.06  --prep_res_sim                          true
% 36.06/5.06  --prep_upred                            true
% 36.06/5.06  --prep_sem_filter                       exhaustive
% 36.06/5.06  --prep_sem_filter_out                   false
% 36.06/5.06  --pred_elim                             true
% 36.06/5.06  --res_sim_input                         true
% 36.06/5.06  --eq_ax_congr_red                       true
% 36.06/5.06  --pure_diseq_elim                       true
% 36.06/5.06  --brand_transform                       false
% 36.06/5.06  --non_eq_to_eq                          false
% 36.06/5.06  --prep_def_merge                        true
% 36.06/5.06  --prep_def_merge_prop_impl              false
% 36.06/5.06  --prep_def_merge_mbd                    true
% 36.06/5.06  --prep_def_merge_tr_red                 false
% 36.06/5.06  --prep_def_merge_tr_cl                  false
% 36.06/5.06  --smt_preprocessing                     true
% 36.06/5.06  --smt_ac_axioms                         fast
% 36.06/5.06  --preprocessed_out                      false
% 36.06/5.06  --preprocessed_stats                    false
% 36.06/5.06  
% 36.06/5.06  ------ Abstraction refinement Options
% 36.06/5.06  
% 36.06/5.06  --abstr_ref                             []
% 36.06/5.06  --abstr_ref_prep                        false
% 36.06/5.06  --abstr_ref_until_sat                   false
% 36.06/5.06  --abstr_ref_sig_restrict                funpre
% 36.06/5.06  --abstr_ref_af_restrict_to_split_sk     false
% 36.06/5.06  --abstr_ref_under                       []
% 36.06/5.06  
% 36.06/5.06  ------ SAT Options
% 36.06/5.06  
% 36.06/5.06  --sat_mode                              false
% 36.06/5.06  --sat_fm_restart_options                ""
% 36.06/5.06  --sat_gr_def                            false
% 36.06/5.06  --sat_epr_types                         true
% 36.06/5.06  --sat_non_cyclic_types                  false
% 36.06/5.06  --sat_finite_models                     false
% 36.06/5.06  --sat_fm_lemmas                         false
% 36.06/5.06  --sat_fm_prep                           false
% 36.06/5.06  --sat_fm_uc_incr                        true
% 36.06/5.06  --sat_out_model                         small
% 36.06/5.06  --sat_out_clauses                       false
% 36.06/5.06  
% 36.06/5.06  ------ QBF Options
% 36.06/5.06  
% 36.06/5.06  --qbf_mode                              false
% 36.06/5.06  --qbf_elim_univ                         false
% 36.06/5.06  --qbf_dom_inst                          none
% 36.06/5.06  --qbf_dom_pre_inst                      false
% 36.06/5.06  --qbf_sk_in                             false
% 36.06/5.06  --qbf_pred_elim                         true
% 36.06/5.06  --qbf_split                             512
% 36.06/5.06  
% 36.06/5.06  ------ BMC1 Options
% 36.06/5.06  
% 36.06/5.06  --bmc1_incremental                      false
% 36.06/5.06  --bmc1_axioms                           reachable_all
% 36.06/5.06  --bmc1_min_bound                        0
% 36.06/5.06  --bmc1_max_bound                        -1
% 36.06/5.06  --bmc1_max_bound_default                -1
% 36.06/5.06  --bmc1_symbol_reachability              true
% 36.06/5.06  --bmc1_property_lemmas                  false
% 36.06/5.06  --bmc1_k_induction                      false
% 36.06/5.06  --bmc1_non_equiv_states                 false
% 36.06/5.06  --bmc1_deadlock                         false
% 36.06/5.06  --bmc1_ucm                              false
% 36.06/5.06  --bmc1_add_unsat_core                   none
% 36.06/5.06  --bmc1_unsat_core_children              false
% 36.06/5.06  --bmc1_unsat_core_extrapolate_axioms    false
% 36.06/5.06  --bmc1_out_stat                         full
% 36.06/5.06  --bmc1_ground_init                      false
% 36.06/5.06  --bmc1_pre_inst_next_state              false
% 36.06/5.06  --bmc1_pre_inst_state                   false
% 36.06/5.06  --bmc1_pre_inst_reach_state             false
% 36.06/5.06  --bmc1_out_unsat_core                   false
% 36.06/5.06  --bmc1_aig_witness_out                  false
% 36.06/5.06  --bmc1_verbose                          false
% 36.06/5.06  --bmc1_dump_clauses_tptp                false
% 36.06/5.06  --bmc1_dump_unsat_core_tptp             false
% 36.06/5.06  --bmc1_dump_file                        -
% 36.06/5.06  --bmc1_ucm_expand_uc_limit              128
% 36.06/5.06  --bmc1_ucm_n_expand_iterations          6
% 36.06/5.06  --bmc1_ucm_extend_mode                  1
% 36.06/5.06  --bmc1_ucm_init_mode                    2
% 36.06/5.06  --bmc1_ucm_cone_mode                    none
% 36.06/5.06  --bmc1_ucm_reduced_relation_type        0
% 36.06/5.06  --bmc1_ucm_relax_model                  4
% 36.06/5.06  --bmc1_ucm_full_tr_after_sat            true
% 36.06/5.06  --bmc1_ucm_expand_neg_assumptions       false
% 36.06/5.06  --bmc1_ucm_layered_model                none
% 36.06/5.06  --bmc1_ucm_max_lemma_size               10
% 36.06/5.06  
% 36.06/5.06  ------ AIG Options
% 36.06/5.06  
% 36.06/5.06  --aig_mode                              false
% 36.06/5.06  
% 36.06/5.06  ------ Instantiation Options
% 36.06/5.06  
% 36.06/5.06  --instantiation_flag                    true
% 36.06/5.06  --inst_sos_flag                         true
% 36.06/5.06  --inst_sos_phase                        true
% 36.06/5.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 36.06/5.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 36.06/5.06  --inst_lit_sel_side                     none
% 36.06/5.06  --inst_solver_per_active                1400
% 36.06/5.06  --inst_solver_calls_frac                1.
% 36.06/5.06  --inst_passive_queue_type               priority_queues
% 36.06/5.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 36.06/5.06  --inst_passive_queues_freq              [25;2]
% 36.06/5.06  --inst_dismatching                      true
% 36.06/5.06  --inst_eager_unprocessed_to_passive     true
% 36.06/5.06  --inst_prop_sim_given                   true
% 36.06/5.06  --inst_prop_sim_new                     false
% 36.06/5.06  --inst_subs_new                         false
% 36.06/5.06  --inst_eq_res_simp                      false
% 36.06/5.06  --inst_subs_given                       false
% 36.06/5.06  --inst_orphan_elimination               true
% 36.06/5.06  --inst_learning_loop_flag               true
% 36.06/5.06  --inst_learning_start                   3000
% 36.06/5.06  --inst_learning_factor                  2
% 36.06/5.06  --inst_start_prop_sim_after_learn       3
% 36.06/5.06  --inst_sel_renew                        solver
% 36.06/5.06  --inst_lit_activity_flag                true
% 36.06/5.06  --inst_restr_to_given                   false
% 36.06/5.06  --inst_activity_threshold               500
% 36.06/5.06  --inst_out_proof                        true
% 36.06/5.06  
% 36.06/5.06  ------ Resolution Options
% 36.06/5.06  
% 36.06/5.06  --resolution_flag                       false
% 36.06/5.06  --res_lit_sel                           adaptive
% 36.06/5.06  --res_lit_sel_side                      none
% 36.06/5.06  --res_ordering                          kbo
% 36.06/5.06  --res_to_prop_solver                    active
% 36.06/5.06  --res_prop_simpl_new                    false
% 36.06/5.06  --res_prop_simpl_given                  true
% 36.06/5.06  --res_passive_queue_type                priority_queues
% 36.06/5.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 36.06/5.06  --res_passive_queues_freq               [15;5]
% 36.06/5.06  --res_forward_subs                      full
% 36.06/5.06  --res_backward_subs                     full
% 36.06/5.06  --res_forward_subs_resolution           true
% 36.06/5.06  --res_backward_subs_resolution          true
% 36.06/5.06  --res_orphan_elimination                true
% 36.06/5.06  --res_time_limit                        2.
% 36.06/5.06  --res_out_proof                         true
% 36.06/5.06  
% 36.06/5.06  ------ Superposition Options
% 36.06/5.06  
% 36.06/5.06  --superposition_flag                    true
% 36.06/5.06  --sup_passive_queue_type                priority_queues
% 36.06/5.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 36.06/5.06  --sup_passive_queues_freq               [8;1;4]
% 36.06/5.06  --demod_completeness_check              fast
% 36.06/5.06  --demod_use_ground                      true
% 36.06/5.06  --sup_to_prop_solver                    passive
% 36.06/5.06  --sup_prop_simpl_new                    true
% 36.06/5.06  --sup_prop_simpl_given                  true
% 36.06/5.06  --sup_fun_splitting                     true
% 36.06/5.06  --sup_smt_interval                      50000
% 36.06/5.06  
% 36.06/5.06  ------ Superposition Simplification Setup
% 36.06/5.06  
% 36.06/5.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 36.06/5.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 36.06/5.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 36.06/5.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 36.06/5.06  --sup_full_triv                         [TrivRules;PropSubs]
% 36.06/5.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 36.06/5.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 36.06/5.06  --sup_immed_triv                        [TrivRules]
% 36.06/5.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 36.06/5.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 36.06/5.06  --sup_immed_bw_main                     []
% 36.06/5.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 36.06/5.06  --sup_input_triv                        [Unflattening;TrivRules]
% 36.06/5.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 36.06/5.06  --sup_input_bw                          []
% 36.06/5.06  
% 36.06/5.06  ------ Combination Options
% 36.06/5.06  
% 36.06/5.06  --comb_res_mult                         3
% 36.06/5.06  --comb_sup_mult                         2
% 36.06/5.06  --comb_inst_mult                        10
% 36.06/5.06  
% 36.06/5.06  ------ Debug Options
% 36.06/5.06  
% 36.06/5.06  --dbg_backtrace                         false
% 36.06/5.06  --dbg_dump_prop_clauses                 false
% 36.06/5.06  --dbg_dump_prop_clauses_file            -
% 36.06/5.06  --dbg_out_stat                          false
% 36.06/5.06  
% 36.06/5.06  
% 36.06/5.06  
% 36.06/5.06  
% 36.06/5.06  ------ Proving...
% 36.06/5.06  
% 36.06/5.06  
% 36.06/5.06  % SZS status Theorem for theBenchmark.p
% 36.06/5.06  
% 36.06/5.06  % SZS output start CNFRefutation for theBenchmark.p
% 36.06/5.06  
% 36.06/5.06  fof(f5,axiom,(
% 36.06/5.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f15,plain,(
% 36.06/5.06    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 36.06/5.06    inference(ennf_transformation,[],[f5])).
% 36.06/5.06  
% 36.06/5.06  fof(f16,plain,(
% 36.06/5.06    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 36.06/5.06    inference(flattening,[],[f15])).
% 36.06/5.06  
% 36.06/5.06  fof(f36,plain,(
% 36.06/5.06    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 36.06/5.06    inference(cnf_transformation,[],[f16])).
% 36.06/5.06  
% 36.06/5.06  fof(f7,axiom,(
% 36.06/5.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f25,plain,(
% 36.06/5.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 36.06/5.06    inference(nnf_transformation,[],[f7])).
% 36.06/5.06  
% 36.06/5.06  fof(f39,plain,(
% 36.06/5.06    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 36.06/5.06    inference(cnf_transformation,[],[f25])).
% 36.06/5.06  
% 36.06/5.06  fof(f6,axiom,(
% 36.06/5.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f17,plain,(
% 36.06/5.06    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 36.06/5.06    inference(ennf_transformation,[],[f6])).
% 36.06/5.06  
% 36.06/5.06  fof(f18,plain,(
% 36.06/5.06    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 36.06/5.06    inference(flattening,[],[f17])).
% 36.06/5.06  
% 36.06/5.06  fof(f37,plain,(
% 36.06/5.06    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 36.06/5.06    inference(cnf_transformation,[],[f18])).
% 36.06/5.06  
% 36.06/5.06  fof(f9,axiom,(
% 36.06/5.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f20,plain,(
% 36.06/5.06    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 36.06/5.06    inference(ennf_transformation,[],[f9])).
% 36.06/5.06  
% 36.06/5.06  fof(f21,plain,(
% 36.06/5.06    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 36.06/5.06    inference(flattening,[],[f20])).
% 36.06/5.06  
% 36.06/5.06  fof(f41,plain,(
% 36.06/5.06    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 36.06/5.06    inference(cnf_transformation,[],[f21])).
% 36.06/5.06  
% 36.06/5.06  fof(f10,conjecture,(
% 36.06/5.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f11,negated_conjecture,(
% 36.06/5.06    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 36.06/5.06    inference(negated_conjecture,[],[f10])).
% 36.06/5.06  
% 36.06/5.06  fof(f22,plain,(
% 36.06/5.06    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 36.06/5.06    inference(ennf_transformation,[],[f11])).
% 36.06/5.06  
% 36.06/5.06  fof(f28,plain,(
% 36.06/5.06    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 36.06/5.06    introduced(choice_axiom,[])).
% 36.06/5.06  
% 36.06/5.06  fof(f27,plain,(
% 36.06/5.06    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 36.06/5.06    introduced(choice_axiom,[])).
% 36.06/5.06  
% 36.06/5.06  fof(f26,plain,(
% 36.06/5.06    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 36.06/5.06    introduced(choice_axiom,[])).
% 36.06/5.06  
% 36.06/5.06  fof(f29,plain,(
% 36.06/5.06    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 36.06/5.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28,f27,f26])).
% 36.06/5.06  
% 36.06/5.06  fof(f42,plain,(
% 36.06/5.06    l1_pre_topc(sK0)),
% 36.06/5.06    inference(cnf_transformation,[],[f29])).
% 36.06/5.06  
% 36.06/5.06  fof(f2,axiom,(
% 36.06/5.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f12,plain,(
% 36.06/5.06    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 36.06/5.06    inference(ennf_transformation,[],[f2])).
% 36.06/5.06  
% 36.06/5.06  fof(f33,plain,(
% 36.06/5.06    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 36.06/5.06    inference(cnf_transformation,[],[f12])).
% 36.06/5.06  
% 36.06/5.06  fof(f4,axiom,(
% 36.06/5.06    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f35,plain,(
% 36.06/5.06    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 36.06/5.06    inference(cnf_transformation,[],[f4])).
% 36.06/5.06  
% 36.06/5.06  fof(f3,axiom,(
% 36.06/5.06    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f13,plain,(
% 36.06/5.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 36.06/5.06    inference(ennf_transformation,[],[f3])).
% 36.06/5.06  
% 36.06/5.06  fof(f14,plain,(
% 36.06/5.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 36.06/5.06    inference(flattening,[],[f13])).
% 36.06/5.06  
% 36.06/5.06  fof(f34,plain,(
% 36.06/5.06    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 36.06/5.06    inference(cnf_transformation,[],[f14])).
% 36.06/5.06  
% 36.06/5.06  fof(f44,plain,(
% 36.06/5.06    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 36.06/5.06    inference(cnf_transformation,[],[f29])).
% 36.06/5.06  
% 36.06/5.06  fof(f38,plain,(
% 36.06/5.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 36.06/5.06    inference(cnf_transformation,[],[f25])).
% 36.06/5.06  
% 36.06/5.06  fof(f43,plain,(
% 36.06/5.06    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 36.06/5.06    inference(cnf_transformation,[],[f29])).
% 36.06/5.06  
% 36.06/5.06  fof(f1,axiom,(
% 36.06/5.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f23,plain,(
% 36.06/5.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 36.06/5.06    inference(nnf_transformation,[],[f1])).
% 36.06/5.06  
% 36.06/5.06  fof(f24,plain,(
% 36.06/5.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 36.06/5.06    inference(flattening,[],[f23])).
% 36.06/5.06  
% 36.06/5.06  fof(f32,plain,(
% 36.06/5.06    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 36.06/5.06    inference(cnf_transformation,[],[f24])).
% 36.06/5.06  
% 36.06/5.06  fof(f30,plain,(
% 36.06/5.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 36.06/5.06    inference(cnf_transformation,[],[f24])).
% 36.06/5.06  
% 36.06/5.06  fof(f47,plain,(
% 36.06/5.06    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 36.06/5.06    inference(equality_resolution,[],[f30])).
% 36.06/5.06  
% 36.06/5.06  fof(f8,axiom,(
% 36.06/5.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 36.06/5.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 36.06/5.06  
% 36.06/5.06  fof(f19,plain,(
% 36.06/5.06    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 36.06/5.06    inference(ennf_transformation,[],[f8])).
% 36.06/5.06  
% 36.06/5.06  fof(f40,plain,(
% 36.06/5.06    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 36.06/5.06    inference(cnf_transformation,[],[f19])).
% 36.06/5.06  
% 36.06/5.06  fof(f45,plain,(
% 36.06/5.06    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 36.06/5.06    inference(cnf_transformation,[],[f29])).
% 36.06/5.06  
% 36.06/5.06  cnf(c_377,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 36.06/5.06      theory(equality) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70064,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,X1)
% 36.06/5.06      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 36.06/5.06      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != X1 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_377]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70236,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 36.06/5.06      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70064]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70430,plain,
% 36.06/5.06      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1)
% 36.06/5.06      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70236]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_126220,plain,
% 36.06/5.06      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 36.06/5.06      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70430]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_6,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 36.06/5.06      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 36.06/5.06      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 36.06/5.06      inference(cnf_transformation,[],[f36]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_8,plain,
% 36.06/5.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 36.06/5.06      inference(cnf_transformation,[],[f39]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_118,plain,
% 36.06/5.06      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 36.06/5.06      inference(prop_impl,[status(thm)],[c_8]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_119,plain,
% 36.06/5.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 36.06/5.06      inference(renaming,[status(thm)],[c_118]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_144,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 36.06/5.06      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
% 36.06/5.06      | ~ r1_tarski(X2,X1) ),
% 36.06/5.06      inference(bin_hyper_res,[status(thm)],[c_6,c_119]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_289,plain,
% 36.06/5.06      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 36.06/5.06      inference(prop_impl,[status(thm)],[c_8]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_290,plain,
% 36.06/5.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 36.06/5.06      inference(renaming,[status(thm)],[c_289]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_314,plain,
% 36.06/5.06      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 36.06/5.06      | ~ r1_tarski(X1,X0)
% 36.06/5.06      | ~ r1_tarski(X2,X0) ),
% 36.06/5.06      inference(bin_hyper_res,[status(thm)],[c_144,c_290]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70761,plain,
% 36.06/5.06      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 36.06/5.06      | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_314]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_87591,plain,
% 36.06/5.06      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),X0),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 36.06/5.06      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70761]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_98463,plain,
% 36.06/5.06      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.06      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 36.06/5.06      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_87591]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_373,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70388,plain,
% 36.06/5.06      ( X0 != X1
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_373]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70888,plain,
% 36.06/5.06      ( X0 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70388]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_72018,plain,
% 36.06/5.06      ( k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70888]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_98257,plain,
% 36.06/5.06      ( k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_72018]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_7,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 36.06/5.06      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 36.06/5.06      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 36.06/5.06      inference(cnf_transformation,[],[f37]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_145,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 36.06/5.06      | ~ r1_tarski(X2,X1)
% 36.06/5.06      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 36.06/5.06      inference(bin_hyper_res,[status(thm)],[c_7,c_119]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_315,plain,
% 36.06/5.06      ( ~ r1_tarski(X0,X1)
% 36.06/5.06      | ~ r1_tarski(X2,X1)
% 36.06/5.06      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 36.06/5.06      inference(bin_hyper_res,[status(thm)],[c_145,c_290]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_74098,plain,
% 36.06/5.06      ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
% 36.06/5.06      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 36.06/5.06      | k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_315]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_79571,plain,
% 36.06/5.06      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
% 36.06/5.06      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
% 36.06/5.06      | k4_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_74098]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_92074,plain,
% 36.06/5.06      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 36.06/5.06      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 36.06/5.06      | k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_79571]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_374,plain,
% 36.06/5.06      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 36.06/5.06      theory(equality) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70270,plain,
% 36.06/5.06      ( ~ r1_tarski(X0,X1)
% 36.06/5.06      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
% 36.06/5.06      | sK2 != X0 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_374]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70557,plain,
% 36.06/5.06      ( ~ r1_tarski(sK2,X0)
% 36.06/5.06      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 36.06/5.06      | sK2 != sK2 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70270]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_71286,plain,
% 36.06/5.06      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | ~ r1_tarski(sK2,k2_xboole_0(X0,X1))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,X1)
% 36.06/5.06      | sK2 != sK2 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70557]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_75964,plain,
% 36.06/5.06      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | ~ r1_tarski(sK2,k2_xboole_0(X0,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,sK2)
% 36.06/5.06      | sK2 != sK2 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_71286]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_89091,plain,
% 36.06/5.06      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 36.06/5.06      | sK2 != sK2 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_75964]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70286,plain,
% 36.06/5.06      ( ~ r1_tarski(X0,X1)
% 36.06/5.06      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
% 36.06/5.06      | sK1 != X0 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_374]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_70568,plain,
% 36.06/5.06      ( ~ r1_tarski(sK1,X0)
% 36.06/5.06      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 36.06/5.06      | sK1 != sK1 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70286]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_71301,plain,
% 36.06/5.06      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | ~ r1_tarski(sK1,k2_xboole_0(X0,X1))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,X1)
% 36.06/5.06      | sK1 != sK1 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_70568]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_73531,plain,
% 36.06/5.06      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | ~ r1_tarski(sK1,k2_xboole_0(sK1,X0))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,X0)
% 36.06/5.06      | sK1 != sK1 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_71301]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_77202,plain,
% 36.06/5.06      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.06      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
% 36.06/5.06      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 36.06/5.06      | sK1 != sK1 ),
% 36.06/5.06      inference(instantiation,[status(thm)],[c_73531]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_11,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 36.06/5.06      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 36.06/5.06      | ~ r1_tarski(X0,X2)
% 36.06/5.06      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 36.06/5.06      | ~ l1_pre_topc(X1) ),
% 36.06/5.06      inference(cnf_transformation,[],[f41]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_15,negated_conjecture,
% 36.06/5.06      ( l1_pre_topc(sK0) ),
% 36.06/5.06      inference(cnf_transformation,[],[f42]) ).
% 36.06/5.06  
% 36.06/5.06  cnf(c_203,plain,
% 36.06/5.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 36.06/5.07      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 36.06/5.07      | ~ r1_tarski(X0,X2)
% 36.06/5.07      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 36.06/5.07      | sK0 != X1 ),
% 36.06/5.07      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_204,plain,
% 36.06/5.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ r1_tarski(X1,X0)
% 36.06/5.07      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 36.06/5.07      inference(unflattening,[status(thm)],[c_203]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_70069,plain,
% 36.06/5.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 36.06/5.07      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_204]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_70218,plain,
% 36.06/5.07      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 36.06/5.07      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_70069]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_70215,plain,
% 36.06/5.07      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 36.06/5.07      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_70069]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_3,plain,
% 36.06/5.07      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 36.06/5.07      inference(cnf_transformation,[],[f33]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_5503,plain,
% 36.06/5.07      ( ~ r1_tarski(sK2,X0) | r1_tarski(sK2,k2_xboole_0(X1,X0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_3]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_25757,plain,
% 36.06/5.07      ( r1_tarski(sK2,k2_xboole_0(X0,sK2)) | ~ r1_tarski(sK2,sK2) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_5503]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_59480,plain,
% 36.06/5.07      ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(sK2,sK2) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_25757]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_5,plain,
% 36.06/5.07      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 36.06/5.07      inference(cnf_transformation,[],[f35]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_8905,plain,
% 36.06/5.07      ( r1_tarski(sK1,k2_xboole_0(sK1,X0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_5]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_47143,plain,
% 36.06/5.07      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_8905]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_4,plain,
% 36.06/5.07      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 36.06/5.07      inference(cnf_transformation,[],[f34]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_832,plain,
% 36.06/5.07      ( ~ r1_tarski(X0,X1)
% 36.06/5.07      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 36.06/5.07      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_4]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1405,plain,
% 36.06/5.07      ( r1_tarski(X0,u1_struct_0(sK0))
% 36.06/5.07      | ~ r1_tarski(X0,sK1)
% 36.06/5.07      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_832]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_2267,plain,
% 36.06/5.07      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 36.06/5.07      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 36.06/5.07      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_1405]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_941,plain,
% 36.06/5.07      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 36.06/5.07      | ~ r1_tarski(X1,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_314]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1399,plain,
% 36.06/5.07      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 36.06/5.07      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_941]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_2251,plain,
% 36.06/5.07      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 36.06/5.07      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_1399]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1394,plain,
% 36.06/5.07      ( r1_tarski(X0,u1_struct_0(sK0))
% 36.06/5.07      | ~ r1_tarski(X0,sK2)
% 36.06/5.07      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_832]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_2243,plain,
% 36.06/5.07      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 36.06/5.07      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 36.06/5.07      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_1394]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_13,negated_conjecture,
% 36.06/5.07      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 36.06/5.07      inference(cnf_transformation,[],[f44]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_699,plain,
% 36.06/5.07      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 36.06/5.07      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_9,plain,
% 36.06/5.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 36.06/5.07      inference(cnf_transformation,[],[f38]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_701,plain,
% 36.06/5.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 36.06/5.07      | r1_tarski(X0,X1) = iProver_top ),
% 36.06/5.07      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1411,plain,
% 36.06/5.07      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 36.06/5.07      inference(superposition,[status(thm)],[c_699,c_701]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_14,negated_conjecture,
% 36.06/5.07      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 36.06/5.07      inference(cnf_transformation,[],[f43]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_698,plain,
% 36.06/5.07      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 36.06/5.07      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1412,plain,
% 36.06/5.07      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 36.06/5.07      inference(superposition,[status(thm)],[c_698,c_701]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_694,plain,
% 36.06/5.07      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 36.06/5.07      | r1_tarski(X1,X0) != iProver_top
% 36.06/5.07      | r1_tarski(X2,X0) != iProver_top ),
% 36.06/5.07      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1571,plain,
% 36.06/5.07      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 36.06/5.07      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 36.06/5.07      inference(superposition,[status(thm)],[c_1412,c_694]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1749,plain,
% 36.06/5.07      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 36.06/5.07      inference(superposition,[status(thm)],[c_1411,c_1571]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_0,plain,
% 36.06/5.07      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 36.06/5.07      inference(cnf_transformation,[],[f32]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1106,plain,
% 36.06/5.07      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_0]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1532,plain,
% 36.06/5.07      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_1106]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1097,plain,
% 36.06/5.07      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_0]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1522,plain,
% 36.06/5.07      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_1097]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1315,plain,
% 36.06/5.07      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 36.06/5.07      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 36.06/5.07      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_315]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_372,plain,( X0 = X0 ),theory(equality) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1161,plain,
% 36.06/5.07      ( k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) = k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_372]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_824,plain,
% 36.06/5.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_9]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1144,plain,
% 36.06/5.07      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_824]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1141,plain,
% 36.06/5.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_824]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_2,plain,
% 36.06/5.07      ( r1_tarski(X0,X0) ),
% 36.06/5.07      inference(cnf_transformation,[],[f47]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1040,plain,
% 36.06/5.07      ( r1_tarski(sK1,sK1) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_2]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_1028,plain,
% 36.06/5.07      ( r1_tarski(sK2,sK2) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_2]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_10,plain,
% 36.06/5.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 36.06/5.07      | r1_tarski(k1_tops_1(X1,X0),X0)
% 36.06/5.07      | ~ l1_pre_topc(X1) ),
% 36.06/5.07      inference(cnf_transformation,[],[f40]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_221,plain,
% 36.06/5.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 36.06/5.07      | r1_tarski(k1_tops_1(X1,X0),X0)
% 36.06/5.07      | sK0 != X1 ),
% 36.06/5.07      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_222,plain,
% 36.06/5.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 36.06/5.07      inference(unflattening,[status(thm)],[c_221]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_743,plain,
% 36.06/5.07      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_222]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_740,plain,
% 36.06/5.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 36.06/5.07      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_222]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_727,plain,
% 36.06/5.07      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 36.06/5.07      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.07      inference(instantiation,[status(thm)],[c_9]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(c_12,negated_conjecture,
% 36.06/5.07      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 36.06/5.07      inference(cnf_transformation,[],[f45]) ).
% 36.06/5.07  
% 36.06/5.07  cnf(contradiction,plain,
% 36.06/5.07      ( $false ),
% 36.06/5.07      inference(minisat,
% 36.06/5.07                [status(thm)],
% 36.06/5.07                [c_126220,c_98463,c_98257,c_92074,c_89091,c_77202,
% 36.06/5.07                 c_70218,c_70215,c_59480,c_47143,c_2267,c_2251,c_2243,
% 36.06/5.07                 c_1749,c_1532,c_1522,c_1315,c_1161,c_1144,c_1141,c_1040,
% 36.06/5.07                 c_1028,c_743,c_740,c_727,c_12,c_13,c_14]) ).
% 36.06/5.07  
% 36.06/5.07  
% 36.06/5.07  % SZS output end CNFRefutation for theBenchmark.p
% 36.06/5.07  
% 36.06/5.07  ------                               Statistics
% 36.06/5.07  
% 36.06/5.07  ------ General
% 36.06/5.07  
% 36.06/5.07  abstr_ref_over_cycles:                  0
% 36.06/5.07  abstr_ref_under_cycles:                 0
% 36.06/5.07  gc_basic_clause_elim:                   0
% 36.06/5.07  forced_gc_time:                         0
% 36.06/5.07  parsing_time:                           0.011
% 36.06/5.07  unif_index_cands_time:                  0.
% 36.06/5.07  unif_index_add_time:                    0.
% 36.06/5.07  orderings_time:                         0.
% 36.06/5.07  out_proof_time:                         0.019
% 36.06/5.07  total_time:                             4.398
% 36.06/5.07  num_of_symbols:                         42
% 36.06/5.07  num_of_terms:                           123875
% 36.06/5.07  
% 36.06/5.07  ------ Preprocessing
% 36.06/5.07  
% 36.06/5.07  num_of_splits:                          0
% 36.06/5.07  num_of_split_atoms:                     0
% 36.06/5.07  num_of_reused_defs:                     0
% 36.06/5.07  num_eq_ax_congr_red:                    6
% 36.06/5.07  num_of_sem_filtered_clauses:            1
% 36.06/5.07  num_of_subtypes:                        0
% 36.06/5.07  monotx_restored_types:                  0
% 36.06/5.07  sat_num_of_epr_types:                   0
% 36.06/5.07  sat_num_of_non_cyclic_types:            0
% 36.06/5.07  sat_guarded_non_collapsed_types:        0
% 36.06/5.07  num_pure_diseq_elim:                    0
% 36.06/5.07  simp_replaced_by:                       0
% 36.06/5.07  res_preprocessed:                       74
% 36.06/5.07  prep_upred:                             0
% 36.06/5.07  prep_unflattend:                        2
% 36.06/5.07  smt_new_axioms:                         0
% 36.06/5.07  pred_elim_cands:                        2
% 36.06/5.07  pred_elim:                              1
% 36.06/5.07  pred_elim_cl:                           1
% 36.06/5.07  pred_elim_cycles:                       3
% 36.06/5.07  merged_defs:                            8
% 36.06/5.07  merged_defs_ncl:                        0
% 36.06/5.07  bin_hyper_res:                          12
% 36.06/5.07  prep_cycles:                            4
% 36.06/5.07  pred_elim_time:                         0.001
% 36.06/5.07  splitting_time:                         0.
% 36.06/5.07  sem_filter_time:                        0.
% 36.06/5.07  monotx_time:                            0.
% 36.06/5.07  subtype_inf_time:                       0.
% 36.06/5.07  
% 36.06/5.07  ------ Problem properties
% 36.06/5.07  
% 36.06/5.07  clauses:                                14
% 36.06/5.07  conjectures:                            3
% 36.06/5.07  epr:                                    3
% 36.06/5.07  horn:                                   14
% 36.06/5.07  ground:                                 3
% 36.06/5.07  unary:                                  5
% 36.06/5.07  binary:                                 4
% 36.06/5.07  lits:                                   29
% 36.06/5.07  lits_eq:                                2
% 36.06/5.07  fd_pure:                                0
% 36.06/5.07  fd_pseudo:                              0
% 36.06/5.07  fd_cond:                                0
% 36.06/5.07  fd_pseudo_cond:                         1
% 36.06/5.07  ac_symbols:                             0
% 36.06/5.07  
% 36.06/5.07  ------ Propositional Solver
% 36.06/5.07  
% 36.06/5.07  prop_solver_calls:                      64
% 36.06/5.07  prop_fast_solver_calls:                 3503
% 36.06/5.07  smt_solver_calls:                       0
% 36.06/5.07  smt_fast_solver_calls:                  0
% 36.06/5.07  prop_num_of_clauses:                    62704
% 36.06/5.07  prop_preprocess_simplified:             63371
% 36.06/5.07  prop_fo_subsumed:                       192
% 36.06/5.07  prop_solver_time:                       0.
% 36.06/5.07  smt_solver_time:                        0.
% 36.06/5.07  smt_fast_solver_time:                   0.
% 36.06/5.07  prop_fast_solver_time:                  0.
% 36.06/5.07  prop_unsat_core_time:                   0.006
% 36.06/5.07  
% 36.06/5.07  ------ QBF
% 36.06/5.07  
% 36.06/5.07  qbf_q_res:                              0
% 36.06/5.07  qbf_num_tautologies:                    0
% 36.06/5.07  qbf_prep_cycles:                        0
% 36.06/5.07  
% 36.06/5.07  ------ BMC1
% 36.06/5.07  
% 36.06/5.07  bmc1_current_bound:                     -1
% 36.06/5.07  bmc1_last_solved_bound:                 -1
% 36.06/5.07  bmc1_unsat_core_size:                   -1
% 36.06/5.07  bmc1_unsat_core_parents_size:           -1
% 36.06/5.07  bmc1_merge_next_fun:                    0
% 36.06/5.07  bmc1_unsat_core_clauses_time:           0.
% 36.06/5.07  
% 36.06/5.07  ------ Instantiation
% 36.06/5.07  
% 36.06/5.07  inst_num_of_clauses:                    4482
% 36.06/5.07  inst_num_in_passive:                    2630
% 36.06/5.07  inst_num_in_active:                     4618
% 36.06/5.07  inst_num_in_unprocessed:                13
% 36.06/5.07  inst_num_of_loops:                      4918
% 36.06/5.07  inst_num_of_learning_restarts:          1
% 36.06/5.07  inst_num_moves_active_passive:          293
% 36.06/5.07  inst_lit_activity:                      0
% 36.06/5.07  inst_lit_activity_moves:                3
% 36.06/5.07  inst_num_tautologies:                   0
% 36.06/5.07  inst_num_prop_implied:                  0
% 36.06/5.07  inst_num_existing_simplified:           0
% 36.06/5.07  inst_num_eq_res_simplified:             0
% 36.06/5.07  inst_num_child_elim:                    0
% 36.06/5.07  inst_num_of_dismatching_blockings:      15882
% 36.06/5.07  inst_num_of_non_proper_insts:           15013
% 36.06/5.07  inst_num_of_duplicates:                 0
% 36.06/5.07  inst_inst_num_from_inst_to_res:         0
% 36.06/5.07  inst_dismatching_checking_time:         0.
% 36.06/5.07  
% 36.06/5.07  ------ Resolution
% 36.06/5.07  
% 36.06/5.07  res_num_of_clauses:                     22
% 36.06/5.07  res_num_in_passive:                     22
% 36.06/5.07  res_num_in_active:                      0
% 36.06/5.07  res_num_of_loops:                       78
% 36.06/5.07  res_forward_subset_subsumed:            670
% 36.06/5.07  res_backward_subset_subsumed:           0
% 36.06/5.07  res_forward_subsumed:                   0
% 36.06/5.07  res_backward_subsumed:                  0
% 36.06/5.07  res_forward_subsumption_resolution:     0
% 36.06/5.07  res_backward_subsumption_resolution:    0
% 36.06/5.07  res_clause_to_clause_subsumption:       222494
% 36.06/5.07  res_orphan_elimination:                 0
% 36.06/5.07  res_tautology_del:                      1678
% 36.06/5.07  res_num_eq_res_simplified:              0
% 36.06/5.07  res_num_sel_changes:                    0
% 36.06/5.07  res_moves_from_active_to_pass:          0
% 36.06/5.07  
% 36.06/5.07  ------ Superposition
% 36.06/5.07  
% 36.06/5.07  sup_time_total:                         0.
% 36.06/5.07  sup_time_generating:                    0.
% 36.06/5.07  sup_time_sim_full:                      0.
% 36.06/5.07  sup_time_sim_immed:                     0.
% 36.06/5.07  
% 36.06/5.07  sup_num_of_clauses:                     11139
% 36.06/5.07  sup_num_in_active:                      923
% 36.06/5.07  sup_num_in_passive:                     10216
% 36.06/5.07  sup_num_of_loops:                       982
% 36.06/5.07  sup_fw_superposition:                   9702
% 36.06/5.07  sup_bw_superposition:                   7299
% 36.06/5.07  sup_immediate_simplified:               3627
% 36.06/5.07  sup_given_eliminated:                   5
% 36.06/5.07  comparisons_done:                       0
% 36.06/5.07  comparisons_avoided:                    0
% 36.06/5.07  
% 36.06/5.07  ------ Simplifications
% 36.06/5.07  
% 36.06/5.07  
% 36.06/5.07  sim_fw_subset_subsumed:                 775
% 36.06/5.07  sim_bw_subset_subsumed:                 184
% 36.06/5.07  sim_fw_subsumed:                        1022
% 36.06/5.07  sim_bw_subsumed:                        388
% 36.06/5.07  sim_fw_subsumption_res:                 0
% 36.06/5.07  sim_bw_subsumption_res:                 0
% 36.06/5.07  sim_tautology_del:                      56
% 36.06/5.07  sim_eq_tautology_del:                   260
% 36.06/5.07  sim_eq_res_simp:                        0
% 36.06/5.07  sim_fw_demodulated:                     313
% 36.06/5.07  sim_bw_demodulated:                     49
% 36.06/5.07  sim_light_normalised:                   1491
% 36.06/5.07  sim_joinable_taut:                      0
% 36.06/5.07  sim_joinable_simp:                      0
% 36.06/5.07  sim_ac_normalised:                      0
% 36.06/5.07  sim_smt_subsumption:                    0
% 36.06/5.07  
%------------------------------------------------------------------------------
