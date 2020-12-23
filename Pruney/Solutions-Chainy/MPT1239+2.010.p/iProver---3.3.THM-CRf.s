%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:54 EST 2020

% Result     : Theorem 51.15s
% Output     : CNFRefutation 51.15s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 307 expanded)
%              Number of clauses        :   78 ( 118 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   20
%              Number of atoms          :  329 ( 963 expanded)
%              Number of equality atoms :   75 ( 136 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f33,f32,f31])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_91029,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(X0,X1)),X1)
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_154899,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X0)
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_91029])).

cnf(c_229868,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_154899])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_859,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_853,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_849,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_845,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_1057,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_849,c_845])).

cnf(c_858,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2512,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_858])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_854,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X3) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X3,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3243,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X3,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2512,c_854])).

cnf(c_11018,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X2) = iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_3243])).

cnf(c_11099,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X4,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11018,c_854])).

cnf(c_33979,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X2) = iProver_top
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_11099])).

cnf(c_34842,plain,
    ( r1_xboole_0(k4_xboole_0(X0,sK2),X1) = iProver_top
    | r1_tarski(X1,k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_33979])).

cnf(c_36515,plain,
    ( r1_xboole_0(k4_xboole_0(X0,sK2),k1_tops_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_34842])).

cnf(c_37673,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X1,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36515,c_854])).

cnf(c_58875,plain,
    ( r1_xboole_0(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_37673])).

cnf(c_60279,plain,
    ( r1_xboole_0(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_58875])).

cnf(c_61819,plain,
    ( r1_xboole_0(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_60279])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_848,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_844,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_844,c_851])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_145,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_176,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_146])).

cnf(c_847,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_2927,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),X1) = k4_xboole_0(k1_tops_1(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_847])).

cnf(c_12795,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_848,c_2927])).

cnf(c_1575,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_851])).

cnf(c_1836,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1575,c_847])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_850,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1975,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1836,c_850])).

cnf(c_12849,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12795,c_1975])).

cnf(c_13314,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_12849])).

cnf(c_63233,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_61819,c_13314])).

cnf(c_63375,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_63233])).

cnf(c_989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1262,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(X0,X1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_4601,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_51037,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4601])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1263,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(k4_xboole_0(X0,X1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3267,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_27169,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3267])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1766,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_27090,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_10937,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_20552,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_10937])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_984,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(X0,X1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(X0,X1),sK1) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_3177,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_16511,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_3177])).

cnf(c_1586,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1575])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_229868,c_63375,c_51037,c_27169,c_27090,c_20552,c_16511,c_1586,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.15/6.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.15/6.99  
% 51.15/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.15/6.99  
% 51.15/6.99  ------  iProver source info
% 51.15/6.99  
% 51.15/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.15/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.15/6.99  git: non_committed_changes: false
% 51.15/6.99  git: last_make_outside_of_git: false
% 51.15/6.99  
% 51.15/6.99  ------ 
% 51.15/6.99  
% 51.15/6.99  ------ Input Options
% 51.15/6.99  
% 51.15/6.99  --out_options                           all
% 51.15/6.99  --tptp_safe_out                         true
% 51.15/6.99  --problem_path                          ""
% 51.15/6.99  --include_path                          ""
% 51.15/6.99  --clausifier                            res/vclausify_rel
% 51.15/6.99  --clausifier_options                    --mode clausify
% 51.15/6.99  --stdin                                 false
% 51.15/6.99  --stats_out                             all
% 51.15/6.99  
% 51.15/6.99  ------ General Options
% 51.15/6.99  
% 51.15/6.99  --fof                                   false
% 51.15/6.99  --time_out_real                         305.
% 51.15/6.99  --time_out_virtual                      -1.
% 51.15/6.99  --symbol_type_check                     false
% 51.15/6.99  --clausify_out                          false
% 51.15/6.99  --sig_cnt_out                           false
% 51.15/6.99  --trig_cnt_out                          false
% 51.15/6.99  --trig_cnt_out_tolerance                1.
% 51.15/6.99  --trig_cnt_out_sk_spl                   false
% 51.15/6.99  --abstr_cl_out                          false
% 51.15/6.99  
% 51.15/6.99  ------ Global Options
% 51.15/6.99  
% 51.15/6.99  --schedule                              default
% 51.15/6.99  --add_important_lit                     false
% 51.15/6.99  --prop_solver_per_cl                    1000
% 51.15/6.99  --min_unsat_core                        false
% 51.15/6.99  --soft_assumptions                      false
% 51.15/6.99  --soft_lemma_size                       3
% 51.15/6.99  --prop_impl_unit_size                   0
% 51.15/6.99  --prop_impl_unit                        []
% 51.15/6.99  --share_sel_clauses                     true
% 51.15/6.99  --reset_solvers                         false
% 51.15/6.99  --bc_imp_inh                            [conj_cone]
% 51.15/6.99  --conj_cone_tolerance                   3.
% 51.15/6.99  --extra_neg_conj                        none
% 51.15/6.99  --large_theory_mode                     true
% 51.15/6.99  --prolific_symb_bound                   200
% 51.15/6.99  --lt_threshold                          2000
% 51.15/6.99  --clause_weak_htbl                      true
% 51.15/6.99  --gc_record_bc_elim                     false
% 51.15/6.99  
% 51.15/6.99  ------ Preprocessing Options
% 51.15/6.99  
% 51.15/6.99  --preprocessing_flag                    true
% 51.15/6.99  --time_out_prep_mult                    0.1
% 51.15/6.99  --splitting_mode                        input
% 51.15/6.99  --splitting_grd                         true
% 51.15/6.99  --splitting_cvd                         false
% 51.15/6.99  --splitting_cvd_svl                     false
% 51.15/6.99  --splitting_nvd                         32
% 51.15/6.99  --sub_typing                            true
% 51.15/6.99  --prep_gs_sim                           true
% 51.15/6.99  --prep_unflatten                        true
% 51.15/6.99  --prep_res_sim                          true
% 51.15/6.99  --prep_upred                            true
% 51.15/6.99  --prep_sem_filter                       exhaustive
% 51.15/6.99  --prep_sem_filter_out                   false
% 51.15/6.99  --pred_elim                             true
% 51.15/6.99  --res_sim_input                         true
% 51.15/6.99  --eq_ax_congr_red                       true
% 51.15/6.99  --pure_diseq_elim                       true
% 51.15/6.99  --brand_transform                       false
% 51.15/6.99  --non_eq_to_eq                          false
% 51.15/6.99  --prep_def_merge                        true
% 51.15/6.99  --prep_def_merge_prop_impl              false
% 51.15/6.99  --prep_def_merge_mbd                    true
% 51.15/6.99  --prep_def_merge_tr_red                 false
% 51.15/6.99  --prep_def_merge_tr_cl                  false
% 51.15/6.99  --smt_preprocessing                     true
% 51.15/6.99  --smt_ac_axioms                         fast
% 51.15/6.99  --preprocessed_out                      false
% 51.15/6.99  --preprocessed_stats                    false
% 51.15/6.99  
% 51.15/6.99  ------ Abstraction refinement Options
% 51.15/6.99  
% 51.15/6.99  --abstr_ref                             []
% 51.15/6.99  --abstr_ref_prep                        false
% 51.15/6.99  --abstr_ref_until_sat                   false
% 51.15/6.99  --abstr_ref_sig_restrict                funpre
% 51.15/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.15/6.99  --abstr_ref_under                       []
% 51.15/6.99  
% 51.15/6.99  ------ SAT Options
% 51.15/6.99  
% 51.15/6.99  --sat_mode                              false
% 51.15/6.99  --sat_fm_restart_options                ""
% 51.15/6.99  --sat_gr_def                            false
% 51.15/6.99  --sat_epr_types                         true
% 51.15/6.99  --sat_non_cyclic_types                  false
% 51.15/6.99  --sat_finite_models                     false
% 51.15/6.99  --sat_fm_lemmas                         false
% 51.15/6.99  --sat_fm_prep                           false
% 51.15/6.99  --sat_fm_uc_incr                        true
% 51.15/6.99  --sat_out_model                         small
% 51.15/6.99  --sat_out_clauses                       false
% 51.15/6.99  
% 51.15/6.99  ------ QBF Options
% 51.15/6.99  
% 51.15/6.99  --qbf_mode                              false
% 51.15/6.99  --qbf_elim_univ                         false
% 51.15/6.99  --qbf_dom_inst                          none
% 51.15/6.99  --qbf_dom_pre_inst                      false
% 51.15/6.99  --qbf_sk_in                             false
% 51.15/6.99  --qbf_pred_elim                         true
% 51.15/6.99  --qbf_split                             512
% 51.15/6.99  
% 51.15/6.99  ------ BMC1 Options
% 51.15/6.99  
% 51.15/6.99  --bmc1_incremental                      false
% 51.15/6.99  --bmc1_axioms                           reachable_all
% 51.15/6.99  --bmc1_min_bound                        0
% 51.15/6.99  --bmc1_max_bound                        -1
% 51.15/6.99  --bmc1_max_bound_default                -1
% 51.15/6.99  --bmc1_symbol_reachability              true
% 51.15/6.99  --bmc1_property_lemmas                  false
% 51.15/6.99  --bmc1_k_induction                      false
% 51.15/6.99  --bmc1_non_equiv_states                 false
% 51.15/6.99  --bmc1_deadlock                         false
% 51.15/6.99  --bmc1_ucm                              false
% 51.15/6.99  --bmc1_add_unsat_core                   none
% 51.15/6.99  --bmc1_unsat_core_children              false
% 51.15/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.15/6.99  --bmc1_out_stat                         full
% 51.15/6.99  --bmc1_ground_init                      false
% 51.15/6.99  --bmc1_pre_inst_next_state              false
% 51.15/6.99  --bmc1_pre_inst_state                   false
% 51.15/6.99  --bmc1_pre_inst_reach_state             false
% 51.15/6.99  --bmc1_out_unsat_core                   false
% 51.15/6.99  --bmc1_aig_witness_out                  false
% 51.15/6.99  --bmc1_verbose                          false
% 51.15/6.99  --bmc1_dump_clauses_tptp                false
% 51.15/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.15/6.99  --bmc1_dump_file                        -
% 51.15/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.15/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.15/6.99  --bmc1_ucm_extend_mode                  1
% 51.15/6.99  --bmc1_ucm_init_mode                    2
% 51.15/6.99  --bmc1_ucm_cone_mode                    none
% 51.15/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.15/6.99  --bmc1_ucm_relax_model                  4
% 51.15/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.15/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.15/6.99  --bmc1_ucm_layered_model                none
% 51.15/6.99  --bmc1_ucm_max_lemma_size               10
% 51.15/6.99  
% 51.15/6.99  ------ AIG Options
% 51.15/6.99  
% 51.15/6.99  --aig_mode                              false
% 51.15/6.99  
% 51.15/6.99  ------ Instantiation Options
% 51.15/6.99  
% 51.15/6.99  --instantiation_flag                    true
% 51.15/6.99  --inst_sos_flag                         false
% 51.15/6.99  --inst_sos_phase                        true
% 51.15/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.15/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.15/6.99  --inst_lit_sel_side                     num_symb
% 51.15/6.99  --inst_solver_per_active                1400
% 51.15/6.99  --inst_solver_calls_frac                1.
% 51.15/6.99  --inst_passive_queue_type               priority_queues
% 51.15/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.15/6.99  --inst_passive_queues_freq              [25;2]
% 51.15/6.99  --inst_dismatching                      true
% 51.15/6.99  --inst_eager_unprocessed_to_passive     true
% 51.15/6.99  --inst_prop_sim_given                   true
% 51.15/6.99  --inst_prop_sim_new                     false
% 51.15/6.99  --inst_subs_new                         false
% 51.15/6.99  --inst_eq_res_simp                      false
% 51.15/6.99  --inst_subs_given                       false
% 51.15/6.99  --inst_orphan_elimination               true
% 51.15/6.99  --inst_learning_loop_flag               true
% 51.15/6.99  --inst_learning_start                   3000
% 51.15/6.99  --inst_learning_factor                  2
% 51.15/6.99  --inst_start_prop_sim_after_learn       3
% 51.15/6.99  --inst_sel_renew                        solver
% 51.15/6.99  --inst_lit_activity_flag                true
% 51.15/6.99  --inst_restr_to_given                   false
% 51.15/6.99  --inst_activity_threshold               500
% 51.15/6.99  --inst_out_proof                        true
% 51.15/6.99  
% 51.15/6.99  ------ Resolution Options
% 51.15/6.99  
% 51.15/6.99  --resolution_flag                       true
% 51.15/6.99  --res_lit_sel                           adaptive
% 51.15/6.99  --res_lit_sel_side                      none
% 51.15/6.99  --res_ordering                          kbo
% 51.15/6.99  --res_to_prop_solver                    active
% 51.15/6.99  --res_prop_simpl_new                    false
% 51.15/6.99  --res_prop_simpl_given                  true
% 51.15/6.99  --res_passive_queue_type                priority_queues
% 51.15/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.15/6.99  --res_passive_queues_freq               [15;5]
% 51.15/6.99  --res_forward_subs                      full
% 51.15/6.99  --res_backward_subs                     full
% 51.15/6.99  --res_forward_subs_resolution           true
% 51.15/6.99  --res_backward_subs_resolution          true
% 51.15/6.99  --res_orphan_elimination                true
% 51.15/6.99  --res_time_limit                        2.
% 51.15/6.99  --res_out_proof                         true
% 51.15/6.99  
% 51.15/6.99  ------ Superposition Options
% 51.15/6.99  
% 51.15/6.99  --superposition_flag                    true
% 51.15/6.99  --sup_passive_queue_type                priority_queues
% 51.15/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.15/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.15/6.99  --demod_completeness_check              fast
% 51.15/6.99  --demod_use_ground                      true
% 51.15/6.99  --sup_to_prop_solver                    passive
% 51.15/6.99  --sup_prop_simpl_new                    true
% 51.15/6.99  --sup_prop_simpl_given                  true
% 51.15/6.99  --sup_fun_splitting                     false
% 51.15/6.99  --sup_smt_interval                      50000
% 51.15/6.99  
% 51.15/6.99  ------ Superposition Simplification Setup
% 51.15/6.99  
% 51.15/6.99  --sup_indices_passive                   []
% 51.15/6.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.15/6.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.15/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.15/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.15/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.15/6.99  --sup_full_bw                           [BwDemod]
% 51.15/6.99  --sup_immed_triv                        [TrivRules]
% 51.15/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.15/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.15/6.99  --sup_immed_bw_main                     []
% 51.15/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.15/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.15/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.15/6.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.15/6.99  
% 51.15/6.99  ------ Combination Options
% 51.15/6.99  
% 51.15/6.99  --comb_res_mult                         3
% 51.15/6.99  --comb_sup_mult                         2
% 51.15/6.99  --comb_inst_mult                        10
% 51.15/6.99  
% 51.15/6.99  ------ Debug Options
% 51.15/6.99  
% 51.15/6.99  --dbg_backtrace                         false
% 51.15/6.99  --dbg_dump_prop_clauses                 false
% 51.15/6.99  --dbg_dump_prop_clauses_file            -
% 51.15/6.99  --dbg_out_stat                          false
% 51.15/6.99  ------ Parsing...
% 51.15/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.15/6.99  
% 51.15/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.15/6.99  
% 51.15/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.15/6.99  
% 51.15/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.15/6.99  ------ Proving...
% 51.15/6.99  ------ Problem Properties 
% 51.15/6.99  
% 51.15/6.99  
% 51.15/6.99  clauses                                 17
% 51.15/6.99  conjectures                             3
% 51.15/6.99  EPR                                     3
% 51.15/6.99  Horn                                    17
% 51.15/6.99  unary                                   5
% 51.15/6.99  binary                                  8
% 51.15/6.99  lits                                    35
% 51.15/6.99  lits eq                                 2
% 51.15/6.99  fd_pure                                 0
% 51.15/6.99  fd_pseudo                               0
% 51.15/6.99  fd_cond                                 0
% 51.15/6.99  fd_pseudo_cond                          1
% 51.15/6.99  AC symbols                              0
% 51.15/6.99  
% 51.15/6.99  ------ Schedule dynamic 5 is on 
% 51.15/6.99  
% 51.15/6.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.15/6.99  
% 51.15/6.99  
% 51.15/6.99  ------ 
% 51.15/6.99  Current options:
% 51.15/6.99  ------ 
% 51.15/6.99  
% 51.15/6.99  ------ Input Options
% 51.15/6.99  
% 51.15/6.99  --out_options                           all
% 51.15/6.99  --tptp_safe_out                         true
% 51.15/6.99  --problem_path                          ""
% 51.15/6.99  --include_path                          ""
% 51.15/6.99  --clausifier                            res/vclausify_rel
% 51.15/6.99  --clausifier_options                    --mode clausify
% 51.15/6.99  --stdin                                 false
% 51.15/6.99  --stats_out                             all
% 51.15/6.99  
% 51.15/6.99  ------ General Options
% 51.15/6.99  
% 51.15/6.99  --fof                                   false
% 51.15/6.99  --time_out_real                         305.
% 51.15/6.99  --time_out_virtual                      -1.
% 51.15/6.99  --symbol_type_check                     false
% 51.15/6.99  --clausify_out                          false
% 51.15/6.99  --sig_cnt_out                           false
% 51.15/6.99  --trig_cnt_out                          false
% 51.15/6.99  --trig_cnt_out_tolerance                1.
% 51.15/6.99  --trig_cnt_out_sk_spl                   false
% 51.15/6.99  --abstr_cl_out                          false
% 51.15/6.99  
% 51.15/6.99  ------ Global Options
% 51.15/6.99  
% 51.15/6.99  --schedule                              default
% 51.15/6.99  --add_important_lit                     false
% 51.15/6.99  --prop_solver_per_cl                    1000
% 51.15/6.99  --min_unsat_core                        false
% 51.15/6.99  --soft_assumptions                      false
% 51.15/6.99  --soft_lemma_size                       3
% 51.15/6.99  --prop_impl_unit_size                   0
% 51.15/6.99  --prop_impl_unit                        []
% 51.15/6.99  --share_sel_clauses                     true
% 51.15/6.99  --reset_solvers                         false
% 51.15/6.99  --bc_imp_inh                            [conj_cone]
% 51.15/6.99  --conj_cone_tolerance                   3.
% 51.15/6.99  --extra_neg_conj                        none
% 51.15/6.99  --large_theory_mode                     true
% 51.15/6.99  --prolific_symb_bound                   200
% 51.15/6.99  --lt_threshold                          2000
% 51.15/6.99  --clause_weak_htbl                      true
% 51.15/6.99  --gc_record_bc_elim                     false
% 51.15/6.99  
% 51.15/6.99  ------ Preprocessing Options
% 51.15/6.99  
% 51.15/6.99  --preprocessing_flag                    true
% 51.15/6.99  --time_out_prep_mult                    0.1
% 51.15/6.99  --splitting_mode                        input
% 51.15/6.99  --splitting_grd                         true
% 51.15/6.99  --splitting_cvd                         false
% 51.15/6.99  --splitting_cvd_svl                     false
% 51.15/6.99  --splitting_nvd                         32
% 51.15/6.99  --sub_typing                            true
% 51.15/6.99  --prep_gs_sim                           true
% 51.15/6.99  --prep_unflatten                        true
% 51.15/6.99  --prep_res_sim                          true
% 51.15/6.99  --prep_upred                            true
% 51.15/6.99  --prep_sem_filter                       exhaustive
% 51.15/6.99  --prep_sem_filter_out                   false
% 51.15/6.99  --pred_elim                             true
% 51.15/6.99  --res_sim_input                         true
% 51.15/6.99  --eq_ax_congr_red                       true
% 51.15/6.99  --pure_diseq_elim                       true
% 51.15/6.99  --brand_transform                       false
% 51.15/6.99  --non_eq_to_eq                          false
% 51.15/6.99  --prep_def_merge                        true
% 51.15/6.99  --prep_def_merge_prop_impl              false
% 51.15/6.99  --prep_def_merge_mbd                    true
% 51.15/6.99  --prep_def_merge_tr_red                 false
% 51.15/6.99  --prep_def_merge_tr_cl                  false
% 51.15/6.99  --smt_preprocessing                     true
% 51.15/6.99  --smt_ac_axioms                         fast
% 51.15/6.99  --preprocessed_out                      false
% 51.15/6.99  --preprocessed_stats                    false
% 51.15/6.99  
% 51.15/6.99  ------ Abstraction refinement Options
% 51.15/6.99  
% 51.15/6.99  --abstr_ref                             []
% 51.15/6.99  --abstr_ref_prep                        false
% 51.15/6.99  --abstr_ref_until_sat                   false
% 51.15/6.99  --abstr_ref_sig_restrict                funpre
% 51.15/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.15/6.99  --abstr_ref_under                       []
% 51.15/6.99  
% 51.15/6.99  ------ SAT Options
% 51.15/6.99  
% 51.15/6.99  --sat_mode                              false
% 51.15/6.99  --sat_fm_restart_options                ""
% 51.15/6.99  --sat_gr_def                            false
% 51.15/6.99  --sat_epr_types                         true
% 51.15/6.99  --sat_non_cyclic_types                  false
% 51.15/6.99  --sat_finite_models                     false
% 51.15/6.99  --sat_fm_lemmas                         false
% 51.15/6.99  --sat_fm_prep                           false
% 51.15/6.99  --sat_fm_uc_incr                        true
% 51.15/6.99  --sat_out_model                         small
% 51.15/6.99  --sat_out_clauses                       false
% 51.15/6.99  
% 51.15/6.99  ------ QBF Options
% 51.15/6.99  
% 51.15/6.99  --qbf_mode                              false
% 51.15/6.99  --qbf_elim_univ                         false
% 51.15/6.99  --qbf_dom_inst                          none
% 51.15/6.99  --qbf_dom_pre_inst                      false
% 51.15/6.99  --qbf_sk_in                             false
% 51.15/6.99  --qbf_pred_elim                         true
% 51.15/6.99  --qbf_split                             512
% 51.15/6.99  
% 51.15/6.99  ------ BMC1 Options
% 51.15/6.99  
% 51.15/6.99  --bmc1_incremental                      false
% 51.15/6.99  --bmc1_axioms                           reachable_all
% 51.15/6.99  --bmc1_min_bound                        0
% 51.15/6.99  --bmc1_max_bound                        -1
% 51.15/6.99  --bmc1_max_bound_default                -1
% 51.15/6.99  --bmc1_symbol_reachability              true
% 51.15/6.99  --bmc1_property_lemmas                  false
% 51.15/6.99  --bmc1_k_induction                      false
% 51.15/6.99  --bmc1_non_equiv_states                 false
% 51.15/6.99  --bmc1_deadlock                         false
% 51.15/6.99  --bmc1_ucm                              false
% 51.15/6.99  --bmc1_add_unsat_core                   none
% 51.15/6.99  --bmc1_unsat_core_children              false
% 51.15/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.15/6.99  --bmc1_out_stat                         full
% 51.15/6.99  --bmc1_ground_init                      false
% 51.15/6.99  --bmc1_pre_inst_next_state              false
% 51.15/6.99  --bmc1_pre_inst_state                   false
% 51.15/6.99  --bmc1_pre_inst_reach_state             false
% 51.15/6.99  --bmc1_out_unsat_core                   false
% 51.15/6.99  --bmc1_aig_witness_out                  false
% 51.15/6.99  --bmc1_verbose                          false
% 51.15/6.99  --bmc1_dump_clauses_tptp                false
% 51.15/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.15/6.99  --bmc1_dump_file                        -
% 51.15/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.15/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.15/6.99  --bmc1_ucm_extend_mode                  1
% 51.15/6.99  --bmc1_ucm_init_mode                    2
% 51.15/6.99  --bmc1_ucm_cone_mode                    none
% 51.15/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.15/6.99  --bmc1_ucm_relax_model                  4
% 51.15/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.15/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.15/6.99  --bmc1_ucm_layered_model                none
% 51.15/6.99  --bmc1_ucm_max_lemma_size               10
% 51.15/6.99  
% 51.15/6.99  ------ AIG Options
% 51.15/6.99  
% 51.15/6.99  --aig_mode                              false
% 51.15/6.99  
% 51.15/6.99  ------ Instantiation Options
% 51.15/6.99  
% 51.15/6.99  --instantiation_flag                    true
% 51.15/6.99  --inst_sos_flag                         false
% 51.15/6.99  --inst_sos_phase                        true
% 51.15/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.15/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.15/6.99  --inst_lit_sel_side                     none
% 51.15/6.99  --inst_solver_per_active                1400
% 51.15/6.99  --inst_solver_calls_frac                1.
% 51.15/6.99  --inst_passive_queue_type               priority_queues
% 51.15/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.15/6.99  --inst_passive_queues_freq              [25;2]
% 51.15/6.99  --inst_dismatching                      true
% 51.15/6.99  --inst_eager_unprocessed_to_passive     true
% 51.15/6.99  --inst_prop_sim_given                   true
% 51.15/6.99  --inst_prop_sim_new                     false
% 51.15/6.99  --inst_subs_new                         false
% 51.15/6.99  --inst_eq_res_simp                      false
% 51.15/6.99  --inst_subs_given                       false
% 51.15/6.99  --inst_orphan_elimination               true
% 51.15/6.99  --inst_learning_loop_flag               true
% 51.15/6.99  --inst_learning_start                   3000
% 51.15/6.99  --inst_learning_factor                  2
% 51.15/6.99  --inst_start_prop_sim_after_learn       3
% 51.15/6.99  --inst_sel_renew                        solver
% 51.15/6.99  --inst_lit_activity_flag                true
% 51.15/6.99  --inst_restr_to_given                   false
% 51.15/6.99  --inst_activity_threshold               500
% 51.15/6.99  --inst_out_proof                        true
% 51.15/6.99  
% 51.15/6.99  ------ Resolution Options
% 51.15/6.99  
% 51.15/6.99  --resolution_flag                       false
% 51.15/6.99  --res_lit_sel                           adaptive
% 51.15/6.99  --res_lit_sel_side                      none
% 51.15/6.99  --res_ordering                          kbo
% 51.15/6.99  --res_to_prop_solver                    active
% 51.15/6.99  --res_prop_simpl_new                    false
% 51.15/6.99  --res_prop_simpl_given                  true
% 51.15/6.99  --res_passive_queue_type                priority_queues
% 51.15/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.15/6.99  --res_passive_queues_freq               [15;5]
% 51.15/6.99  --res_forward_subs                      full
% 51.15/6.99  --res_backward_subs                     full
% 51.15/6.99  --res_forward_subs_resolution           true
% 51.15/6.99  --res_backward_subs_resolution          true
% 51.15/6.99  --res_orphan_elimination                true
% 51.15/6.99  --res_time_limit                        2.
% 51.15/6.99  --res_out_proof                         true
% 51.15/6.99  
% 51.15/6.99  ------ Superposition Options
% 51.15/6.99  
% 51.15/6.99  --superposition_flag                    true
% 51.15/6.99  --sup_passive_queue_type                priority_queues
% 51.15/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.15/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.15/6.99  --demod_completeness_check              fast
% 51.15/6.99  --demod_use_ground                      true
% 51.15/6.99  --sup_to_prop_solver                    passive
% 51.15/6.99  --sup_prop_simpl_new                    true
% 51.15/6.99  --sup_prop_simpl_given                  true
% 51.15/6.99  --sup_fun_splitting                     false
% 51.15/6.99  --sup_smt_interval                      50000
% 51.15/6.99  
% 51.15/6.99  ------ Superposition Simplification Setup
% 51.15/6.99  
% 51.15/6.99  --sup_indices_passive                   []
% 51.15/6.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.15/6.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.15/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.15/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.15/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.15/6.99  --sup_full_bw                           [BwDemod]
% 51.15/6.99  --sup_immed_triv                        [TrivRules]
% 51.15/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.15/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.15/6.99  --sup_immed_bw_main                     []
% 51.15/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.15/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.15/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.15/6.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.15/6.99  
% 51.15/6.99  ------ Combination Options
% 51.15/6.99  
% 51.15/6.99  --comb_res_mult                         3
% 51.15/6.99  --comb_sup_mult                         2
% 51.15/6.99  --comb_inst_mult                        10
% 51.15/6.99  
% 51.15/6.99  ------ Debug Options
% 51.15/6.99  
% 51.15/6.99  --dbg_backtrace                         false
% 51.15/6.99  --dbg_dump_prop_clauses                 false
% 51.15/6.99  --dbg_dump_prop_clauses_file            -
% 51.15/6.99  --dbg_out_stat                          false
% 51.15/6.99  
% 51.15/6.99  
% 51.15/6.99  
% 51.15/6.99  
% 51.15/6.99  ------ Proving...
% 51.15/6.99  
% 51.15/6.99  
% 51.15/6.99  % SZS status Theorem for theBenchmark.p
% 51.15/6.99  
% 51.15/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.15/6.99  
% 51.15/6.99  fof(f2,axiom,(
% 51.15/6.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f15,plain,(
% 51.15/6.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 51.15/6.99    inference(ennf_transformation,[],[f2])).
% 51.15/6.99  
% 51.15/6.99  fof(f39,plain,(
% 51.15/6.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 51.15/6.99    inference(cnf_transformation,[],[f15])).
% 51.15/6.99  
% 51.15/6.99  fof(f1,axiom,(
% 51.15/6.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f28,plain,(
% 51.15/6.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.15/6.99    inference(nnf_transformation,[],[f1])).
% 51.15/6.99  
% 51.15/6.99  fof(f29,plain,(
% 51.15/6.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.15/6.99    inference(flattening,[],[f28])).
% 51.15/6.99  
% 51.15/6.99  fof(f36,plain,(
% 51.15/6.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 51.15/6.99    inference(cnf_transformation,[],[f29])).
% 51.15/6.99  
% 51.15/6.99  fof(f54,plain,(
% 51.15/6.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.15/6.99    inference(equality_resolution,[],[f36])).
% 51.15/6.99  
% 51.15/6.99  fof(f6,axiom,(
% 51.15/6.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f19,plain,(
% 51.15/6.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 51.15/6.99    inference(ennf_transformation,[],[f6])).
% 51.15/6.99  
% 51.15/6.99  fof(f20,plain,(
% 51.15/6.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 51.15/6.99    inference(flattening,[],[f19])).
% 51.15/6.99  
% 51.15/6.99  fof(f43,plain,(
% 51.15/6.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 51.15/6.99    inference(cnf_transformation,[],[f20])).
% 51.15/6.99  
% 51.15/6.99  fof(f12,conjecture,(
% 51.15/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f13,negated_conjecture,(
% 51.15/6.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 51.15/6.99    inference(negated_conjecture,[],[f12])).
% 51.15/6.99  
% 51.15/6.99  fof(f14,plain,(
% 51.15/6.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 51.15/6.99    inference(pure_predicate_removal,[],[f13])).
% 51.15/6.99  
% 51.15/6.99  fof(f27,plain,(
% 51.15/6.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 51.15/6.99    inference(ennf_transformation,[],[f14])).
% 51.15/6.99  
% 51.15/6.99  fof(f33,plain,(
% 51.15/6.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 51.15/6.99    introduced(choice_axiom,[])).
% 51.15/6.99  
% 51.15/6.99  fof(f32,plain,(
% 51.15/6.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 51.15/6.99    introduced(choice_axiom,[])).
% 51.15/6.99  
% 51.15/6.99  fof(f31,plain,(
% 51.15/6.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 51.15/6.99    introduced(choice_axiom,[])).
% 51.15/6.99  
% 51.15/6.99  fof(f34,plain,(
% 51.15/6.99    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 51.15/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f33,f32,f31])).
% 51.15/6.99  
% 51.15/6.99  fof(f52,plain,(
% 51.15/6.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 51.15/6.99    inference(cnf_transformation,[],[f34])).
% 51.15/6.99  
% 51.15/6.99  fof(f10,axiom,(
% 51.15/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f24,plain,(
% 51.15/6.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.15/6.99    inference(ennf_transformation,[],[f10])).
% 51.15/6.99  
% 51.15/6.99  fof(f48,plain,(
% 51.15/6.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.15/6.99    inference(cnf_transformation,[],[f24])).
% 51.15/6.99  
% 51.15/6.99  fof(f50,plain,(
% 51.15/6.99    l1_pre_topc(sK0)),
% 51.15/6.99    inference(cnf_transformation,[],[f34])).
% 51.15/6.99  
% 51.15/6.99  fof(f5,axiom,(
% 51.15/6.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f17,plain,(
% 51.15/6.99    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 51.15/6.99    inference(ennf_transformation,[],[f5])).
% 51.15/6.99  
% 51.15/6.99  fof(f18,plain,(
% 51.15/6.99    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 51.15/6.99    inference(flattening,[],[f17])).
% 51.15/6.99  
% 51.15/6.99  fof(f42,plain,(
% 51.15/6.99    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 51.15/6.99    inference(cnf_transformation,[],[f18])).
% 51.15/6.99  
% 51.15/6.99  fof(f51,plain,(
% 51.15/6.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 51.15/6.99    inference(cnf_transformation,[],[f34])).
% 51.15/6.99  
% 51.15/6.99  fof(f9,axiom,(
% 51.15/6.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f22,plain,(
% 51.15/6.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 51.15/6.99    inference(ennf_transformation,[],[f9])).
% 51.15/6.99  
% 51.15/6.99  fof(f23,plain,(
% 51.15/6.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 51.15/6.99    inference(flattening,[],[f22])).
% 51.15/6.99  
% 51.15/6.99  fof(f47,plain,(
% 51.15/6.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.15/6.99    inference(cnf_transformation,[],[f23])).
% 51.15/6.99  
% 51.15/6.99  fof(f8,axiom,(
% 51.15/6.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f30,plain,(
% 51.15/6.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 51.15/6.99    inference(nnf_transformation,[],[f8])).
% 51.15/6.99  
% 51.15/6.99  fof(f45,plain,(
% 51.15/6.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 51.15/6.99    inference(cnf_transformation,[],[f30])).
% 51.15/6.99  
% 51.15/6.99  fof(f7,axiom,(
% 51.15/6.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f21,plain,(
% 51.15/6.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.15/6.99    inference(ennf_transformation,[],[f7])).
% 51.15/6.99  
% 51.15/6.99  fof(f44,plain,(
% 51.15/6.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.15/6.99    inference(cnf_transformation,[],[f21])).
% 51.15/6.99  
% 51.15/6.99  fof(f46,plain,(
% 51.15/6.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 51.15/6.99    inference(cnf_transformation,[],[f30])).
% 51.15/6.99  
% 51.15/6.99  fof(f53,plain,(
% 51.15/6.99    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 51.15/6.99    inference(cnf_transformation,[],[f34])).
% 51.15/6.99  
% 51.15/6.99  fof(f3,axiom,(
% 51.15/6.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f16,plain,(
% 51.15/6.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 51.15/6.99    inference(ennf_transformation,[],[f3])).
% 51.15/6.99  
% 51.15/6.99  fof(f40,plain,(
% 51.15/6.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 51.15/6.99    inference(cnf_transformation,[],[f16])).
% 51.15/6.99  
% 51.15/6.99  fof(f4,axiom,(
% 51.15/6.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f41,plain,(
% 51.15/6.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.15/6.99    inference(cnf_transformation,[],[f4])).
% 51.15/6.99  
% 51.15/6.99  fof(f11,axiom,(
% 51.15/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 51.15/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.15/6.99  
% 51.15/6.99  fof(f25,plain,(
% 51.15/6.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.15/6.99    inference(ennf_transformation,[],[f11])).
% 51.15/6.99  
% 51.15/6.99  fof(f26,plain,(
% 51.15/6.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.15/6.99    inference(flattening,[],[f25])).
% 51.15/6.99  
% 51.15/6.99  fof(f49,plain,(
% 51.15/6.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.15/6.99    inference(cnf_transformation,[],[f26])).
% 51.15/6.99  
% 51.15/6.99  cnf(c_3,plain,
% 51.15/6.99      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 51.15/6.99      inference(cnf_transformation,[],[f39]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_91029,plain,
% 51.15/6.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(X0,X1)),X1)
% 51.15/6.99      | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
% 51.15/6.99      inference(instantiation,[status(thm)],[c_3]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_154899,plain,
% 51.15/6.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X0)
% 51.15/6.99      | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) ),
% 51.15/6.99      inference(instantiation,[status(thm)],[c_91029]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_229868,plain,
% 51.15/6.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
% 51.15/6.99      | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
% 51.15/6.99      inference(instantiation,[status(thm)],[c_154899]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_1,plain,
% 51.15/6.99      ( r1_tarski(X0,X0) ),
% 51.15/6.99      inference(cnf_transformation,[],[f54]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_859,plain,
% 51.15/6.99      ( r1_tarski(X0,X0) = iProver_top ),
% 51.15/6.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_8,plain,
% 51.15/6.99      ( ~ r1_xboole_0(X0,X1)
% 51.15/6.99      | ~ r1_tarski(X0,X2)
% 51.15/6.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 51.15/6.99      inference(cnf_transformation,[],[f43]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_853,plain,
% 51.15/6.99      ( r1_xboole_0(X0,X1) != iProver_top
% 51.15/6.99      | r1_tarski(X0,X2) != iProver_top
% 51.15/6.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) = iProver_top ),
% 51.15/6.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_16,negated_conjecture,
% 51.15/6.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 51.15/6.99      inference(cnf_transformation,[],[f52]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_849,plain,
% 51.15/6.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.15/6.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_13,plain,
% 51.15/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/6.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 51.15/6.99      | ~ l1_pre_topc(X1) ),
% 51.15/6.99      inference(cnf_transformation,[],[f48]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_18,negated_conjecture,
% 51.15/6.99      ( l1_pre_topc(sK0) ),
% 51.15/6.99      inference(cnf_transformation,[],[f50]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_263,plain,
% 51.15/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/6.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 51.15/6.99      | sK0 != X1 ),
% 51.15/6.99      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_264,plain,
% 51.15/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/6.99      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 51.15/6.99      inference(unflattening,[status(thm)],[c_263]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_845,plain,
% 51.15/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.15/6.99      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 51.15/6.99      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_1057,plain,
% 51.15/6.99      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 51.15/6.99      inference(superposition,[status(thm)],[c_849,c_845]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_858,plain,
% 51.15/6.99      ( r1_xboole_0(X0,X1) = iProver_top
% 51.15/6.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 51.15/6.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_2512,plain,
% 51.15/6.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 51.15/6.99      inference(superposition,[status(thm)],[c_859,c_858]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_7,plain,
% 51.15/6.99      ( ~ r1_xboole_0(X0,X1)
% 51.15/6.99      | r1_xboole_0(X2,X3)
% 51.15/6.99      | ~ r1_tarski(X2,X0)
% 51.15/6.99      | ~ r1_tarski(X3,X1) ),
% 51.15/6.99      inference(cnf_transformation,[],[f42]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_854,plain,
% 51.15/6.99      ( r1_xboole_0(X0,X1) != iProver_top
% 51.15/6.99      | r1_xboole_0(X2,X3) = iProver_top
% 51.15/6.99      | r1_tarski(X2,X0) != iProver_top
% 51.15/6.99      | r1_tarski(X3,X1) != iProver_top ),
% 51.15/6.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_3243,plain,
% 51.15/6.99      ( r1_xboole_0(X0,X1) = iProver_top
% 51.15/6.99      | r1_tarski(X1,X2) != iProver_top
% 51.15/6.99      | r1_tarski(X0,k4_xboole_0(X3,X2)) != iProver_top ),
% 51.15/6.99      inference(superposition,[status(thm)],[c_2512,c_854]) ).
% 51.15/6.99  
% 51.15/6.99  cnf(c_11018,plain,
% 51.15/6.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X2) = iProver_top
% 51.15/6.99      | r1_tarski(X2,X1) != iProver_top ),
% 51.15/6.99      inference(superposition,[status(thm)],[c_859,c_3243]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_11099,plain,
% 51.15/7.00      ( r1_xboole_0(X0,X1) = iProver_top
% 51.15/7.00      | r1_tarski(X2,X3) != iProver_top
% 51.15/7.00      | r1_tarski(X1,X2) != iProver_top
% 51.15/7.00      | r1_tarski(X0,k4_xboole_0(X4,X3)) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_11018,c_854]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_33979,plain,
% 51.15/7.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X2) = iProver_top
% 51.15/7.00      | r1_tarski(X3,X1) != iProver_top
% 51.15/7.00      | r1_tarski(X2,X3) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_859,c_11099]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_34842,plain,
% 51.15/7.00      ( r1_xboole_0(k4_xboole_0(X0,sK2),X1) = iProver_top
% 51.15/7.00      | r1_tarski(X1,k1_tops_1(sK0,sK2)) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_1057,c_33979]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_36515,plain,
% 51.15/7.00      ( r1_xboole_0(k4_xboole_0(X0,sK2),k1_tops_1(sK0,sK2)) = iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_859,c_34842]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_37673,plain,
% 51.15/7.00      ( r1_xboole_0(X0,X1) = iProver_top
% 51.15/7.00      | r1_tarski(X1,k1_tops_1(sK0,sK2)) != iProver_top
% 51.15/7.00      | r1_tarski(X0,k4_xboole_0(X2,sK2)) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_36515,c_854]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_58875,plain,
% 51.15/7.00      ( r1_xboole_0(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 51.15/7.00      | r1_tarski(X0,k4_xboole_0(X1,sK2)) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_859,c_37673]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_60279,plain,
% 51.15/7.00      ( r1_xboole_0(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 51.15/7.00      | r1_xboole_0(X0,sK2) != iProver_top
% 51.15/7.00      | r1_tarski(X0,X1) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_853,c_58875]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_61819,plain,
% 51.15/7.00      ( r1_xboole_0(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 51.15/7.00      | r1_xboole_0(X0,sK2) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_859,c_60279]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_17,negated_conjecture,
% 51.15/7.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 51.15/7.00      inference(cnf_transformation,[],[f51]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_848,plain,
% 51.15/7.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.15/7.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_12,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/7.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/7.00      | ~ l1_pre_topc(X1) ),
% 51.15/7.00      inference(cnf_transformation,[],[f47]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_275,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/7.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/7.00      | sK0 != X1 ),
% 51.15/7.00      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_276,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 51.15/7.00      inference(unflattening,[status(thm)],[c_275]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_844,plain,
% 51.15/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.15/7.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.15/7.00      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_11,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 51.15/7.00      inference(cnf_transformation,[],[f45]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_851,plain,
% 51.15/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.15/7.00      | r1_tarski(X0,X1) = iProver_top ),
% 51.15/7.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1576,plain,
% 51.15/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) = iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_844,c_851]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_9,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.15/7.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 51.15/7.00      inference(cnf_transformation,[],[f44]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_10,plain,
% 51.15/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 51.15/7.00      inference(cnf_transformation,[],[f46]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_145,plain,
% 51.15/7.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 51.15/7.00      inference(prop_impl,[status(thm)],[c_10]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_146,plain,
% 51.15/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 51.15/7.00      inference(renaming,[status(thm)],[c_145]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_176,plain,
% 51.15/7.00      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 51.15/7.00      inference(bin_hyper_res,[status(thm)],[c_9,c_146]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_847,plain,
% 51.15/7.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 51.15/7.00      | r1_tarski(X1,X0) != iProver_top ),
% 51.15/7.00      inference(predicate_to_equality,[status(thm)],[c_176]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_2927,plain,
% 51.15/7.00      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),X1) = k4_xboole_0(k1_tops_1(sK0,X0),X1)
% 51.15/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_1576,c_847]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_12795,plain,
% 51.15/7.00      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_848,c_2927]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1575,plain,
% 51.15/7.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_848,c_851]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1836,plain,
% 51.15/7.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_1575,c_847]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_15,negated_conjecture,
% 51.15/7.00      ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 51.15/7.00      inference(cnf_transformation,[],[f53]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_850,plain,
% 51.15/7.00      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 51.15/7.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1975,plain,
% 51.15/7.00      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 51.15/7.00      inference(demodulation,[status(thm)],[c_1836,c_850]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_12849,plain,
% 51.15/7.00      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 51.15/7.00      inference(demodulation,[status(thm)],[c_12795,c_1975]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_13314,plain,
% 51.15/7.00      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_853,c_12849]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_63233,plain,
% 51.15/7.00      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
% 51.15/7.00      inference(superposition,[status(thm)],[c_61819,c_13314]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_63375,plain,
% 51.15/7.00      ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
% 51.15/7.00      | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
% 51.15/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_63233]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_989,plain,
% 51.15/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_10]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1262,plain,
% 51.15/7.00      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ r1_tarski(k4_xboole_0(X0,X1),u1_struct_0(sK0)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_989]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_4601,plain,
% 51.15/7.00      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_1262]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_51037,plain,
% 51.15/7.00      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_4601]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_5,plain,
% 51.15/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 51.15/7.00      inference(cnf_transformation,[],[f40]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1263,plain,
% 51.15/7.00      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 51.15/7.00      | r1_tarski(k4_xboole_0(X0,X1),u1_struct_0(sK0)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_5]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_3267,plain,
% 51.15/7.00      ( r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
% 51.15/7.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_1263]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_27169,plain,
% 51.15/7.00      ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 51.15/7.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_3267]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_6,plain,
% 51.15/7.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 51.15/7.00      inference(cnf_transformation,[],[f41]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1766,plain,
% 51.15/7.00      ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_6]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_27090,plain,
% 51.15/7.00      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_1766]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_10937,plain,
% 51.15/7.00      ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_264]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_20552,plain,
% 51.15/7.00      ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_10937]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_14,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/7.00      | ~ r1_tarski(X0,X2)
% 51.15/7.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 51.15/7.00      | ~ l1_pre_topc(X1) ),
% 51.15/7.00      inference(cnf_transformation,[],[f49]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_245,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 51.15/7.00      | ~ r1_tarski(X0,X2)
% 51.15/7.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 51.15/7.00      | sK0 != X1 ),
% 51.15/7.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_246,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ r1_tarski(X1,X0)
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 51.15/7.00      inference(unflattening,[status(thm)],[c_245]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_984,plain,
% 51.15/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ r1_tarski(X0,sK1)
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_246]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1171,plain,
% 51.15/7.00      ( ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(X0,X1)),k1_tops_1(sK0,sK1))
% 51.15/7.00      | ~ r1_tarski(k4_xboole_0(X0,X1),sK1) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_984]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_3177,plain,
% 51.15/7.00      ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k1_tops_1(sK0,sK1))
% 51.15/7.00      | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_1171]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_16511,plain,
% 51.15/7.00      ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.15/7.00      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
% 51.15/7.00      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 51.15/7.00      inference(instantiation,[status(thm)],[c_3177]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(c_1586,plain,
% 51.15/7.00      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 51.15/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_1575]) ).
% 51.15/7.00  
% 51.15/7.00  cnf(contradiction,plain,
% 51.15/7.00      ( $false ),
% 51.15/7.00      inference(minisat,
% 51.15/7.00                [status(thm)],
% 51.15/7.00                [c_229868,c_63375,c_51037,c_27169,c_27090,c_20552,
% 51.15/7.00                 c_16511,c_1586,c_17]) ).
% 51.15/7.00  
% 51.15/7.00  
% 51.15/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.15/7.00  
% 51.15/7.00  ------                               Statistics
% 51.15/7.00  
% 51.15/7.00  ------ General
% 51.15/7.00  
% 51.15/7.00  abstr_ref_over_cycles:                  0
% 51.15/7.00  abstr_ref_under_cycles:                 0
% 51.15/7.00  gc_basic_clause_elim:                   0
% 51.15/7.00  forced_gc_time:                         0
% 51.15/7.00  parsing_time:                           0.007
% 51.15/7.00  unif_index_cands_time:                  0.
% 51.15/7.00  unif_index_add_time:                    0.
% 51.15/7.00  orderings_time:                         0.
% 51.15/7.00  out_proof_time:                         0.022
% 51.15/7.00  total_time:                             6.277
% 51.15/7.00  num_of_symbols:                         43
% 51.15/7.00  num_of_terms:                           221022
% 51.15/7.00  
% 51.15/7.00  ------ Preprocessing
% 51.15/7.00  
% 51.15/7.00  num_of_splits:                          0
% 51.15/7.00  num_of_split_atoms:                     0
% 51.15/7.00  num_of_reused_defs:                     0
% 51.15/7.00  num_eq_ax_congr_red:                    12
% 51.15/7.00  num_of_sem_filtered_clauses:            1
% 51.15/7.00  num_of_subtypes:                        0
% 51.15/7.00  monotx_restored_types:                  0
% 51.15/7.00  sat_num_of_epr_types:                   0
% 51.15/7.00  sat_num_of_non_cyclic_types:            0
% 51.15/7.00  sat_guarded_non_collapsed_types:        0
% 51.15/7.00  num_pure_diseq_elim:                    0
% 51.15/7.00  simp_replaced_by:                       0
% 51.15/7.00  res_preprocessed:                       86
% 51.15/7.00  prep_upred:                             0
% 51.15/7.00  prep_unflattend:                        3
% 51.15/7.00  smt_new_axioms:                         0
% 51.15/7.00  pred_elim_cands:                        3
% 51.15/7.00  pred_elim:                              1
% 51.15/7.00  pred_elim_cl:                           1
% 51.15/7.00  pred_elim_cycles:                       3
% 51.15/7.00  merged_defs:                            8
% 51.15/7.00  merged_defs_ncl:                        0
% 51.15/7.00  bin_hyper_res:                          9
% 51.15/7.00  prep_cycles:                            4
% 51.15/7.00  pred_elim_time:                         0.
% 51.15/7.00  splitting_time:                         0.
% 51.15/7.00  sem_filter_time:                        0.
% 51.15/7.00  monotx_time:                            0.
% 51.15/7.00  subtype_inf_time:                       0.
% 51.15/7.00  
% 51.15/7.00  ------ Problem properties
% 51.15/7.00  
% 51.15/7.00  clauses:                                17
% 51.15/7.00  conjectures:                            3
% 51.15/7.00  epr:                                    3
% 51.15/7.00  horn:                                   17
% 51.15/7.00  ground:                                 3
% 51.15/7.00  unary:                                  5
% 51.15/7.00  binary:                                 8
% 51.15/7.00  lits:                                   35
% 51.15/7.00  lits_eq:                                2
% 51.15/7.00  fd_pure:                                0
% 51.15/7.00  fd_pseudo:                              0
% 51.15/7.00  fd_cond:                                0
% 51.15/7.00  fd_pseudo_cond:                         1
% 51.15/7.00  ac_symbols:                             0
% 51.15/7.00  
% 51.15/7.00  ------ Propositional Solver
% 51.15/7.00  
% 51.15/7.00  prop_solver_calls:                      76
% 51.15/7.00  prop_fast_solver_calls:                 3280
% 51.15/7.00  smt_solver_calls:                       0
% 51.15/7.00  smt_fast_solver_calls:                  0
% 51.15/7.00  prop_num_of_clauses:                    75438
% 51.15/7.00  prop_preprocess_simplified:             107259
% 51.15/7.00  prop_fo_subsumed:                       82
% 51.15/7.00  prop_solver_time:                       0.
% 51.15/7.00  smt_solver_time:                        0.
% 51.15/7.00  smt_fast_solver_time:                   0.
% 51.15/7.00  prop_fast_solver_time:                  0.
% 51.15/7.00  prop_unsat_core_time:                   0.009
% 51.15/7.00  
% 51.15/7.00  ------ QBF
% 51.15/7.00  
% 51.15/7.00  qbf_q_res:                              0
% 51.15/7.00  qbf_num_tautologies:                    0
% 51.15/7.00  qbf_prep_cycles:                        0
% 51.15/7.00  
% 51.15/7.00  ------ BMC1
% 51.15/7.00  
% 51.15/7.00  bmc1_current_bound:                     -1
% 51.15/7.00  bmc1_last_solved_bound:                 -1
% 51.15/7.00  bmc1_unsat_core_size:                   -1
% 51.15/7.00  bmc1_unsat_core_parents_size:           -1
% 51.15/7.00  bmc1_merge_next_fun:                    0
% 51.15/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.15/7.00  
% 51.15/7.00  ------ Instantiation
% 51.15/7.00  
% 51.15/7.00  inst_num_of_clauses:                    8231
% 51.15/7.00  inst_num_in_passive:                    4672
% 51.15/7.00  inst_num_in_active:                     5302
% 51.15/7.00  inst_num_in_unprocessed:                1094
% 51.15/7.00  inst_num_of_loops:                      5649
% 51.15/7.00  inst_num_of_learning_restarts:          1
% 51.15/7.00  inst_num_moves_active_passive:          343
% 51.15/7.00  inst_lit_activity:                      0
% 51.15/7.00  inst_lit_activity_moves:                4
% 51.15/7.00  inst_num_tautologies:                   0
% 51.15/7.00  inst_num_prop_implied:                  0
% 51.15/7.00  inst_num_existing_simplified:           0
% 51.15/7.00  inst_num_eq_res_simplified:             0
% 51.15/7.00  inst_num_child_elim:                    0
% 51.15/7.00  inst_num_of_dismatching_blockings:      16678
% 51.15/7.00  inst_num_of_non_proper_insts:           21897
% 51.15/7.00  inst_num_of_duplicates:                 0
% 51.15/7.00  inst_inst_num_from_inst_to_res:         0
% 51.15/7.00  inst_dismatching_checking_time:         0.
% 51.15/7.00  
% 51.15/7.00  ------ Resolution
% 51.15/7.00  
% 51.15/7.00  res_num_of_clauses:                     25
% 51.15/7.00  res_num_in_passive:                     25
% 51.15/7.00  res_num_in_active:                      0
% 51.15/7.00  res_num_of_loops:                       90
% 51.15/7.00  res_forward_subset_subsumed:            1603
% 51.15/7.00  res_backward_subset_subsumed:           52
% 51.15/7.00  res_forward_subsumed:                   0
% 51.15/7.00  res_backward_subsumed:                  0
% 51.15/7.00  res_forward_subsumption_resolution:     0
% 51.15/7.00  res_backward_subsumption_resolution:    0
% 51.15/7.00  res_clause_to_clause_subsumption:       213938
% 51.15/7.00  res_orphan_elimination:                 0
% 51.15/7.00  res_tautology_del:                      1266
% 51.15/7.00  res_num_eq_res_simplified:              0
% 51.15/7.00  res_num_sel_changes:                    0
% 51.15/7.00  res_moves_from_active_to_pass:          0
% 51.15/7.00  
% 51.15/7.00  ------ Superposition
% 51.15/7.00  
% 51.15/7.00  sup_time_total:                         0.
% 51.15/7.00  sup_time_generating:                    0.
% 51.15/7.00  sup_time_sim_full:                      0.
% 51.15/7.00  sup_time_sim_immed:                     0.
% 51.15/7.00  
% 51.15/7.00  sup_num_of_clauses:                     8746
% 51.15/7.00  sup_num_in_active:                      1094
% 51.15/7.00  sup_num_in_passive:                     7652
% 51.15/7.00  sup_num_of_loops:                       1128
% 51.15/7.00  sup_fw_superposition:                   21026
% 51.15/7.00  sup_bw_superposition:                   9357
% 51.15/7.00  sup_immediate_simplified:               9486
% 51.15/7.00  sup_given_eliminated:                   3
% 51.15/7.00  comparisons_done:                       0
% 51.15/7.00  comparisons_avoided:                    0
% 51.15/7.00  
% 51.15/7.00  ------ Simplifications
% 51.15/7.00  
% 51.15/7.00  
% 51.15/7.00  sim_fw_subset_subsumed:                 236
% 51.15/7.00  sim_bw_subset_subsumed:                 179
% 51.15/7.00  sim_fw_subsumed:                        5046
% 51.15/7.00  sim_bw_subsumed:                        950
% 51.15/7.00  sim_fw_subsumption_res:                 0
% 51.15/7.00  sim_bw_subsumption_res:                 0
% 51.15/7.00  sim_tautology_del:                      83
% 51.15/7.00  sim_eq_tautology_del:                   586
% 51.15/7.00  sim_eq_res_simp:                        0
% 51.15/7.00  sim_fw_demodulated:                     3718
% 51.15/7.00  sim_bw_demodulated:                     45
% 51.15/7.00  sim_light_normalised:                   1117
% 51.15/7.00  sim_joinable_taut:                      0
% 51.15/7.00  sim_joinable_simp:                      0
% 51.15/7.00  sim_ac_normalised:                      0
% 51.15/7.00  sim_smt_subsumption:                    0
% 51.15/7.00  
%------------------------------------------------------------------------------
