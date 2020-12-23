%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:51 EST 2020

% Result     : Theorem 35.62s
% Output     : CNFRefutation 35.62s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 285 expanded)
%              Number of clauses        :   89 ( 125 expanded)
%              Number of leaves         :   16 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  379 ( 922 expanded)
%              Number of equality atoms :   77 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

cnf(c_371,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_107022,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_107664,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_107022])).

cnf(c_108803,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(X0,X1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,X1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_107664])).

cnf(c_115165,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(X0,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_108803])).

cnf(c_137307,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_115165])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_108050,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X0,X1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(X0,X1))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_112244,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_108050])).

cnf(c_134655,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_112244])).

cnf(c_106124,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_106173,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_106124])).

cnf(c_107377,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_106173])).

cnf(c_134121,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_107377])).

cnf(c_107038,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_107675,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_107038])).

cnf(c_108818,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(X0,X1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,X1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_107675])).

cnf(c_111330,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,X0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,X0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_108818])).

cnf(c_118826,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_111330])).

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

cnf(c_8976,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_59558,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8976])).

cnf(c_59555,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8976])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5575,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_40940,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5575])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_5098,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k2_xboole_0(sK1,sK2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_40404,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5098])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15581,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_741,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_824,plain,
    ( m1_subset_1(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_3748,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_1032,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1888,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(k2_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_2309,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1888])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_821,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1404,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_2242,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_1398,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_2195,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_693,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_695,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1450,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_695])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_692,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1451,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_695])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_118,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_118])).

cnf(c_145,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_119])).

cnf(c_289,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_314,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_145,c_290])).

cnf(c_689,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1637,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_689])).

cnf(c_1816,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1450,c_1637])).

cnf(c_1552,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1140,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1539,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1123,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1524,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_369,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1285,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_813,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1166,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_1163,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1039,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1017,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_908,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_369])).

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

cnf(c_738,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_735,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_137307,c_134655,c_134121,c_118826,c_59558,c_59555,c_40940,c_40404,c_15581,c_3748,c_2309,c_2242,c_2195,c_1816,c_1552,c_1539,c_1524,c_1285,c_1166,c_1163,c_1039,c_1017,c_908,c_738,c_735,c_12,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:08:02 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 35.62/4.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.62/4.98  
% 35.62/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.62/4.98  
% 35.62/4.98  ------  iProver source info
% 35.62/4.98  
% 35.62/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.62/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.62/4.98  git: non_committed_changes: false
% 35.62/4.98  git: last_make_outside_of_git: false
% 35.62/4.98  
% 35.62/4.98  ------ 
% 35.62/4.98  
% 35.62/4.98  ------ Input Options
% 35.62/4.98  
% 35.62/4.98  --out_options                           all
% 35.62/4.98  --tptp_safe_out                         true
% 35.62/4.98  --problem_path                          ""
% 35.62/4.98  --include_path                          ""
% 35.62/4.98  --clausifier                            res/vclausify_rel
% 35.62/4.98  --clausifier_options                    ""
% 35.62/4.98  --stdin                                 false
% 35.62/4.98  --stats_out                             all
% 35.62/4.98  
% 35.62/4.98  ------ General Options
% 35.62/4.98  
% 35.62/4.98  --fof                                   false
% 35.62/4.98  --time_out_real                         305.
% 35.62/4.98  --time_out_virtual                      -1.
% 35.62/4.98  --symbol_type_check                     false
% 35.62/4.98  --clausify_out                          false
% 35.62/4.98  --sig_cnt_out                           false
% 35.62/4.98  --trig_cnt_out                          false
% 35.62/4.98  --trig_cnt_out_tolerance                1.
% 35.62/4.98  --trig_cnt_out_sk_spl                   false
% 35.62/4.98  --abstr_cl_out                          false
% 35.62/4.98  
% 35.62/4.98  ------ Global Options
% 35.62/4.98  
% 35.62/4.98  --schedule                              default
% 35.62/4.98  --add_important_lit                     false
% 35.62/4.98  --prop_solver_per_cl                    1000
% 35.62/4.98  --min_unsat_core                        false
% 35.62/4.98  --soft_assumptions                      false
% 35.62/4.98  --soft_lemma_size                       3
% 35.62/4.98  --prop_impl_unit_size                   0
% 35.62/4.98  --prop_impl_unit                        []
% 35.62/4.98  --share_sel_clauses                     true
% 35.62/4.98  --reset_solvers                         false
% 35.62/4.98  --bc_imp_inh                            [conj_cone]
% 35.62/4.98  --conj_cone_tolerance                   3.
% 35.62/4.98  --extra_neg_conj                        none
% 35.62/4.98  --large_theory_mode                     true
% 35.62/4.98  --prolific_symb_bound                   200
% 35.62/4.98  --lt_threshold                          2000
% 35.62/4.98  --clause_weak_htbl                      true
% 35.62/4.98  --gc_record_bc_elim                     false
% 35.62/4.98  
% 35.62/4.98  ------ Preprocessing Options
% 35.62/4.98  
% 35.62/4.98  --preprocessing_flag                    true
% 35.62/4.98  --time_out_prep_mult                    0.1
% 35.62/4.98  --splitting_mode                        input
% 35.62/4.98  --splitting_grd                         true
% 35.62/4.98  --splitting_cvd                         false
% 35.62/4.98  --splitting_cvd_svl                     false
% 35.62/4.98  --splitting_nvd                         32
% 35.62/4.98  --sub_typing                            true
% 35.62/4.98  --prep_gs_sim                           true
% 35.62/4.98  --prep_unflatten                        true
% 35.62/4.98  --prep_res_sim                          true
% 35.62/4.98  --prep_upred                            true
% 35.62/4.98  --prep_sem_filter                       exhaustive
% 35.62/4.98  --prep_sem_filter_out                   false
% 35.62/4.98  --pred_elim                             true
% 35.62/4.98  --res_sim_input                         true
% 35.62/4.98  --eq_ax_congr_red                       true
% 35.62/4.98  --pure_diseq_elim                       true
% 35.62/4.98  --brand_transform                       false
% 35.62/4.98  --non_eq_to_eq                          false
% 35.62/4.98  --prep_def_merge                        true
% 35.62/4.98  --prep_def_merge_prop_impl              false
% 35.62/4.98  --prep_def_merge_mbd                    true
% 35.62/4.98  --prep_def_merge_tr_red                 false
% 35.62/4.98  --prep_def_merge_tr_cl                  false
% 35.62/4.98  --smt_preprocessing                     true
% 35.62/4.98  --smt_ac_axioms                         fast
% 35.62/4.98  --preprocessed_out                      false
% 35.62/4.98  --preprocessed_stats                    false
% 35.62/4.98  
% 35.62/4.98  ------ Abstraction refinement Options
% 35.62/4.98  
% 35.62/4.98  --abstr_ref                             []
% 35.62/4.98  --abstr_ref_prep                        false
% 35.62/4.98  --abstr_ref_until_sat                   false
% 35.62/4.98  --abstr_ref_sig_restrict                funpre
% 35.62/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.62/4.98  --abstr_ref_under                       []
% 35.62/4.98  
% 35.62/4.98  ------ SAT Options
% 35.62/4.98  
% 35.62/4.98  --sat_mode                              false
% 35.62/4.98  --sat_fm_restart_options                ""
% 35.62/4.98  --sat_gr_def                            false
% 35.62/4.98  --sat_epr_types                         true
% 35.62/4.98  --sat_non_cyclic_types                  false
% 35.62/4.98  --sat_finite_models                     false
% 35.62/4.98  --sat_fm_lemmas                         false
% 35.62/4.98  --sat_fm_prep                           false
% 35.62/4.98  --sat_fm_uc_incr                        true
% 35.62/4.98  --sat_out_model                         small
% 35.62/4.98  --sat_out_clauses                       false
% 35.62/4.98  
% 35.62/4.98  ------ QBF Options
% 35.62/4.98  
% 35.62/4.98  --qbf_mode                              false
% 35.62/4.98  --qbf_elim_univ                         false
% 35.62/4.98  --qbf_dom_inst                          none
% 35.62/4.98  --qbf_dom_pre_inst                      false
% 35.62/4.98  --qbf_sk_in                             false
% 35.62/4.98  --qbf_pred_elim                         true
% 35.62/4.98  --qbf_split                             512
% 35.62/4.98  
% 35.62/4.98  ------ BMC1 Options
% 35.62/4.98  
% 35.62/4.98  --bmc1_incremental                      false
% 35.62/4.98  --bmc1_axioms                           reachable_all
% 35.62/4.98  --bmc1_min_bound                        0
% 35.62/4.98  --bmc1_max_bound                        -1
% 35.62/4.98  --bmc1_max_bound_default                -1
% 35.62/4.98  --bmc1_symbol_reachability              true
% 35.62/4.98  --bmc1_property_lemmas                  false
% 35.62/4.98  --bmc1_k_induction                      false
% 35.62/4.98  --bmc1_non_equiv_states                 false
% 35.62/4.98  --bmc1_deadlock                         false
% 35.62/4.98  --bmc1_ucm                              false
% 35.62/4.98  --bmc1_add_unsat_core                   none
% 35.62/4.98  --bmc1_unsat_core_children              false
% 35.62/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.62/4.98  --bmc1_out_stat                         full
% 35.62/4.98  --bmc1_ground_init                      false
% 35.62/4.98  --bmc1_pre_inst_next_state              false
% 35.62/4.98  --bmc1_pre_inst_state                   false
% 35.62/4.98  --bmc1_pre_inst_reach_state             false
% 35.62/4.98  --bmc1_out_unsat_core                   false
% 35.62/4.98  --bmc1_aig_witness_out                  false
% 35.62/4.98  --bmc1_verbose                          false
% 35.62/4.98  --bmc1_dump_clauses_tptp                false
% 35.62/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.62/4.98  --bmc1_dump_file                        -
% 35.62/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.62/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.62/4.98  --bmc1_ucm_extend_mode                  1
% 35.62/4.98  --bmc1_ucm_init_mode                    2
% 35.62/4.98  --bmc1_ucm_cone_mode                    none
% 35.62/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.62/4.98  --bmc1_ucm_relax_model                  4
% 35.62/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.62/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.62/4.98  --bmc1_ucm_layered_model                none
% 35.62/4.98  --bmc1_ucm_max_lemma_size               10
% 35.62/4.98  
% 35.62/4.98  ------ AIG Options
% 35.62/4.98  
% 35.62/4.98  --aig_mode                              false
% 35.62/4.98  
% 35.62/4.98  ------ Instantiation Options
% 35.62/4.98  
% 35.62/4.98  --instantiation_flag                    true
% 35.62/4.98  --inst_sos_flag                         true
% 35.62/4.98  --inst_sos_phase                        true
% 35.62/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.62/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.62/4.98  --inst_lit_sel_side                     num_symb
% 35.62/4.98  --inst_solver_per_active                1400
% 35.62/4.98  --inst_solver_calls_frac                1.
% 35.62/4.98  --inst_passive_queue_type               priority_queues
% 35.62/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.62/4.98  --inst_passive_queues_freq              [25;2]
% 35.62/4.98  --inst_dismatching                      true
% 35.62/4.98  --inst_eager_unprocessed_to_passive     true
% 35.62/4.98  --inst_prop_sim_given                   true
% 35.62/4.98  --inst_prop_sim_new                     false
% 35.62/4.98  --inst_subs_new                         false
% 35.62/4.98  --inst_eq_res_simp                      false
% 35.62/4.98  --inst_subs_given                       false
% 35.62/4.98  --inst_orphan_elimination               true
% 35.62/4.98  --inst_learning_loop_flag               true
% 35.62/4.98  --inst_learning_start                   3000
% 35.62/4.98  --inst_learning_factor                  2
% 35.62/4.98  --inst_start_prop_sim_after_learn       3
% 35.62/4.98  --inst_sel_renew                        solver
% 35.62/4.98  --inst_lit_activity_flag                true
% 35.62/4.98  --inst_restr_to_given                   false
% 35.62/4.98  --inst_activity_threshold               500
% 35.62/4.98  --inst_out_proof                        true
% 35.62/4.98  
% 35.62/4.98  ------ Resolution Options
% 35.62/4.98  
% 35.62/4.98  --resolution_flag                       true
% 35.62/4.98  --res_lit_sel                           adaptive
% 35.62/4.98  --res_lit_sel_side                      none
% 35.62/4.98  --res_ordering                          kbo
% 35.62/4.98  --res_to_prop_solver                    active
% 35.62/4.98  --res_prop_simpl_new                    false
% 35.62/4.98  --res_prop_simpl_given                  true
% 35.62/4.98  --res_passive_queue_type                priority_queues
% 35.62/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.62/4.98  --res_passive_queues_freq               [15;5]
% 35.62/4.98  --res_forward_subs                      full
% 35.62/4.98  --res_backward_subs                     full
% 35.62/4.98  --res_forward_subs_resolution           true
% 35.62/4.98  --res_backward_subs_resolution          true
% 35.62/4.98  --res_orphan_elimination                true
% 35.62/4.98  --res_time_limit                        2.
% 35.62/4.98  --res_out_proof                         true
% 35.62/4.98  
% 35.62/4.98  ------ Superposition Options
% 35.62/4.98  
% 35.62/4.98  --superposition_flag                    true
% 35.62/4.98  --sup_passive_queue_type                priority_queues
% 35.62/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.62/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.62/4.98  --demod_completeness_check              fast
% 35.62/4.98  --demod_use_ground                      true
% 35.62/4.98  --sup_to_prop_solver                    passive
% 35.62/4.98  --sup_prop_simpl_new                    true
% 35.62/4.98  --sup_prop_simpl_given                  true
% 35.62/4.98  --sup_fun_splitting                     true
% 35.62/4.98  --sup_smt_interval                      50000
% 35.62/4.98  
% 35.62/4.98  ------ Superposition Simplification Setup
% 35.62/4.98  
% 35.62/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.62/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.62/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.62/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.62/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.62/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.62/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.62/4.98  --sup_immed_triv                        [TrivRules]
% 35.62/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.62/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.62/4.98  --sup_immed_bw_main                     []
% 35.62/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.62/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.62/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.62/4.98  --sup_input_bw                          []
% 35.62/4.98  
% 35.62/4.98  ------ Combination Options
% 35.62/4.98  
% 35.62/4.98  --comb_res_mult                         3
% 35.62/4.98  --comb_sup_mult                         2
% 35.62/4.98  --comb_inst_mult                        10
% 35.62/4.98  
% 35.62/4.98  ------ Debug Options
% 35.62/4.98  
% 35.62/4.98  --dbg_backtrace                         false
% 35.62/4.98  --dbg_dump_prop_clauses                 false
% 35.62/4.98  --dbg_dump_prop_clauses_file            -
% 35.62/4.98  --dbg_out_stat                          false
% 35.62/4.98  ------ Parsing...
% 35.62/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.62/4.98  
% 35.62/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.62/4.98  
% 35.62/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.62/4.98  
% 35.62/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.62/4.98  ------ Proving...
% 35.62/4.98  ------ Problem Properties 
% 35.62/4.98  
% 35.62/4.98  
% 35.62/4.98  clauses                                 14
% 35.62/4.98  conjectures                             3
% 35.62/4.98  EPR                                     3
% 35.62/4.98  Horn                                    14
% 35.62/4.98  unary                                   5
% 35.62/4.98  binary                                  4
% 35.62/4.98  lits                                    29
% 35.62/4.98  lits eq                                 2
% 35.62/4.98  fd_pure                                 0
% 35.62/4.98  fd_pseudo                               0
% 35.62/4.98  fd_cond                                 0
% 35.62/4.98  fd_pseudo_cond                          1
% 35.62/4.98  AC symbols                              0
% 35.62/4.98  
% 35.62/4.98  ------ Schedule dynamic 5 is on 
% 35.62/4.98  
% 35.62/4.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.62/4.98  
% 35.62/4.98  
% 35.62/4.98  ------ 
% 35.62/4.98  Current options:
% 35.62/4.98  ------ 
% 35.62/4.98  
% 35.62/4.98  ------ Input Options
% 35.62/4.98  
% 35.62/4.98  --out_options                           all
% 35.62/4.98  --tptp_safe_out                         true
% 35.62/4.98  --problem_path                          ""
% 35.62/4.98  --include_path                          ""
% 35.62/4.98  --clausifier                            res/vclausify_rel
% 35.62/4.98  --clausifier_options                    ""
% 35.62/4.98  --stdin                                 false
% 35.62/4.98  --stats_out                             all
% 35.62/4.98  
% 35.62/4.98  ------ General Options
% 35.62/4.98  
% 35.62/4.98  --fof                                   false
% 35.62/4.98  --time_out_real                         305.
% 35.62/4.98  --time_out_virtual                      -1.
% 35.62/4.98  --symbol_type_check                     false
% 35.62/4.98  --clausify_out                          false
% 35.62/4.98  --sig_cnt_out                           false
% 35.62/4.98  --trig_cnt_out                          false
% 35.62/4.98  --trig_cnt_out_tolerance                1.
% 35.62/4.98  --trig_cnt_out_sk_spl                   false
% 35.62/4.98  --abstr_cl_out                          false
% 35.62/4.98  
% 35.62/4.98  ------ Global Options
% 35.62/4.98  
% 35.62/4.98  --schedule                              default
% 35.62/4.98  --add_important_lit                     false
% 35.62/4.98  --prop_solver_per_cl                    1000
% 35.62/4.98  --min_unsat_core                        false
% 35.62/4.98  --soft_assumptions                      false
% 35.62/4.98  --soft_lemma_size                       3
% 35.62/4.98  --prop_impl_unit_size                   0
% 35.62/4.98  --prop_impl_unit                        []
% 35.62/4.98  --share_sel_clauses                     true
% 35.62/4.98  --reset_solvers                         false
% 35.62/4.98  --bc_imp_inh                            [conj_cone]
% 35.62/4.98  --conj_cone_tolerance                   3.
% 35.62/4.98  --extra_neg_conj                        none
% 35.62/4.98  --large_theory_mode                     true
% 35.62/4.98  --prolific_symb_bound                   200
% 35.62/4.98  --lt_threshold                          2000
% 35.62/4.98  --clause_weak_htbl                      true
% 35.62/4.98  --gc_record_bc_elim                     false
% 35.62/4.98  
% 35.62/4.98  ------ Preprocessing Options
% 35.62/4.98  
% 35.62/4.98  --preprocessing_flag                    true
% 35.62/4.98  --time_out_prep_mult                    0.1
% 35.62/4.98  --splitting_mode                        input
% 35.62/4.98  --splitting_grd                         true
% 35.62/4.98  --splitting_cvd                         false
% 35.62/4.98  --splitting_cvd_svl                     false
% 35.62/4.98  --splitting_nvd                         32
% 35.62/4.98  --sub_typing                            true
% 35.62/4.98  --prep_gs_sim                           true
% 35.62/4.98  --prep_unflatten                        true
% 35.62/4.98  --prep_res_sim                          true
% 35.62/4.98  --prep_upred                            true
% 35.62/4.98  --prep_sem_filter                       exhaustive
% 35.62/4.98  --prep_sem_filter_out                   false
% 35.62/4.98  --pred_elim                             true
% 35.62/4.98  --res_sim_input                         true
% 35.62/4.98  --eq_ax_congr_red                       true
% 35.62/4.98  --pure_diseq_elim                       true
% 35.62/4.98  --brand_transform                       false
% 35.62/4.98  --non_eq_to_eq                          false
% 35.62/4.98  --prep_def_merge                        true
% 35.62/4.98  --prep_def_merge_prop_impl              false
% 35.62/4.98  --prep_def_merge_mbd                    true
% 35.62/4.98  --prep_def_merge_tr_red                 false
% 35.62/4.98  --prep_def_merge_tr_cl                  false
% 35.62/4.98  --smt_preprocessing                     true
% 35.62/4.98  --smt_ac_axioms                         fast
% 35.62/4.98  --preprocessed_out                      false
% 35.62/4.98  --preprocessed_stats                    false
% 35.62/4.98  
% 35.62/4.98  ------ Abstraction refinement Options
% 35.62/4.98  
% 35.62/4.98  --abstr_ref                             []
% 35.62/4.98  --abstr_ref_prep                        false
% 35.62/4.98  --abstr_ref_until_sat                   false
% 35.62/4.98  --abstr_ref_sig_restrict                funpre
% 35.62/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.62/4.98  --abstr_ref_under                       []
% 35.62/4.98  
% 35.62/4.98  ------ SAT Options
% 35.62/4.98  
% 35.62/4.98  --sat_mode                              false
% 35.62/4.98  --sat_fm_restart_options                ""
% 35.62/4.98  --sat_gr_def                            false
% 35.62/4.98  --sat_epr_types                         true
% 35.62/4.98  --sat_non_cyclic_types                  false
% 35.62/4.98  --sat_finite_models                     false
% 35.62/4.98  --sat_fm_lemmas                         false
% 35.62/4.98  --sat_fm_prep                           false
% 35.62/4.98  --sat_fm_uc_incr                        true
% 35.62/4.98  --sat_out_model                         small
% 35.62/4.98  --sat_out_clauses                       false
% 35.62/4.98  
% 35.62/4.98  ------ QBF Options
% 35.62/4.98  
% 35.62/4.98  --qbf_mode                              false
% 35.62/4.98  --qbf_elim_univ                         false
% 35.62/4.98  --qbf_dom_inst                          none
% 35.62/4.98  --qbf_dom_pre_inst                      false
% 35.62/4.98  --qbf_sk_in                             false
% 35.62/4.98  --qbf_pred_elim                         true
% 35.62/4.98  --qbf_split                             512
% 35.62/4.98  
% 35.62/4.98  ------ BMC1 Options
% 35.62/4.98  
% 35.62/4.98  --bmc1_incremental                      false
% 35.62/4.98  --bmc1_axioms                           reachable_all
% 35.62/4.98  --bmc1_min_bound                        0
% 35.62/4.98  --bmc1_max_bound                        -1
% 35.62/4.98  --bmc1_max_bound_default                -1
% 35.62/4.98  --bmc1_symbol_reachability              true
% 35.62/4.98  --bmc1_property_lemmas                  false
% 35.62/4.98  --bmc1_k_induction                      false
% 35.62/4.98  --bmc1_non_equiv_states                 false
% 35.62/4.98  --bmc1_deadlock                         false
% 35.62/4.98  --bmc1_ucm                              false
% 35.62/4.98  --bmc1_add_unsat_core                   none
% 35.62/4.98  --bmc1_unsat_core_children              false
% 35.62/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.62/4.98  --bmc1_out_stat                         full
% 35.62/4.98  --bmc1_ground_init                      false
% 35.62/4.98  --bmc1_pre_inst_next_state              false
% 35.62/4.98  --bmc1_pre_inst_state                   false
% 35.62/4.98  --bmc1_pre_inst_reach_state             false
% 35.62/4.98  --bmc1_out_unsat_core                   false
% 35.62/4.98  --bmc1_aig_witness_out                  false
% 35.62/4.98  --bmc1_verbose                          false
% 35.62/4.98  --bmc1_dump_clauses_tptp                false
% 35.62/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.62/4.98  --bmc1_dump_file                        -
% 35.62/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.62/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.62/4.98  --bmc1_ucm_extend_mode                  1
% 35.62/4.98  --bmc1_ucm_init_mode                    2
% 35.62/4.98  --bmc1_ucm_cone_mode                    none
% 35.62/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.62/4.98  --bmc1_ucm_relax_model                  4
% 35.62/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.62/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.62/4.98  --bmc1_ucm_layered_model                none
% 35.62/4.98  --bmc1_ucm_max_lemma_size               10
% 35.62/4.98  
% 35.62/4.98  ------ AIG Options
% 35.62/4.98  
% 35.62/4.98  --aig_mode                              false
% 35.62/4.98  
% 35.62/4.98  ------ Instantiation Options
% 35.62/4.98  
% 35.62/4.98  --instantiation_flag                    true
% 35.62/4.98  --inst_sos_flag                         true
% 35.62/4.98  --inst_sos_phase                        true
% 35.62/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.62/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.62/4.98  --inst_lit_sel_side                     none
% 35.62/4.98  --inst_solver_per_active                1400
% 35.62/4.98  --inst_solver_calls_frac                1.
% 35.62/4.98  --inst_passive_queue_type               priority_queues
% 35.62/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.62/4.98  --inst_passive_queues_freq              [25;2]
% 35.62/4.98  --inst_dismatching                      true
% 35.62/4.98  --inst_eager_unprocessed_to_passive     true
% 35.62/4.98  --inst_prop_sim_given                   true
% 35.62/4.98  --inst_prop_sim_new                     false
% 35.62/4.98  --inst_subs_new                         false
% 35.62/4.98  --inst_eq_res_simp                      false
% 35.62/4.98  --inst_subs_given                       false
% 35.62/4.98  --inst_orphan_elimination               true
% 35.62/4.98  --inst_learning_loop_flag               true
% 35.62/4.98  --inst_learning_start                   3000
% 35.62/4.98  --inst_learning_factor                  2
% 35.62/4.98  --inst_start_prop_sim_after_learn       3
% 35.62/4.98  --inst_sel_renew                        solver
% 35.62/4.98  --inst_lit_activity_flag                true
% 35.62/4.98  --inst_restr_to_given                   false
% 35.62/4.98  --inst_activity_threshold               500
% 35.62/4.98  --inst_out_proof                        true
% 35.62/4.98  
% 35.62/4.98  ------ Resolution Options
% 35.62/4.98  
% 35.62/4.98  --resolution_flag                       false
% 35.62/4.98  --res_lit_sel                           adaptive
% 35.62/4.98  --res_lit_sel_side                      none
% 35.62/4.98  --res_ordering                          kbo
% 35.62/4.98  --res_to_prop_solver                    active
% 35.62/4.98  --res_prop_simpl_new                    false
% 35.62/4.98  --res_prop_simpl_given                  true
% 35.62/4.98  --res_passive_queue_type                priority_queues
% 35.62/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.62/4.98  --res_passive_queues_freq               [15;5]
% 35.62/4.98  --res_forward_subs                      full
% 35.62/4.98  --res_backward_subs                     full
% 35.62/4.98  --res_forward_subs_resolution           true
% 35.62/4.98  --res_backward_subs_resolution          true
% 35.62/4.98  --res_orphan_elimination                true
% 35.62/4.98  --res_time_limit                        2.
% 35.62/4.98  --res_out_proof                         true
% 35.62/4.98  
% 35.62/4.98  ------ Superposition Options
% 35.62/4.98  
% 35.62/4.98  --superposition_flag                    true
% 35.62/4.98  --sup_passive_queue_type                priority_queues
% 35.62/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.62/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.62/4.98  --demod_completeness_check              fast
% 35.62/4.98  --demod_use_ground                      true
% 35.62/4.98  --sup_to_prop_solver                    passive
% 35.62/4.98  --sup_prop_simpl_new                    true
% 35.62/4.98  --sup_prop_simpl_given                  true
% 35.62/4.98  --sup_fun_splitting                     true
% 35.62/4.98  --sup_smt_interval                      50000
% 35.62/4.98  
% 35.62/4.98  ------ Superposition Simplification Setup
% 35.62/4.98  
% 35.62/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.62/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.62/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.62/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.62/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.62/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.62/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.62/4.98  --sup_immed_triv                        [TrivRules]
% 35.62/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.62/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.62/4.98  --sup_immed_bw_main                     []
% 35.62/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.62/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.62/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.62/4.98  --sup_input_bw                          []
% 35.62/4.98  
% 35.62/4.98  ------ Combination Options
% 35.62/4.98  
% 35.62/4.98  --comb_res_mult                         3
% 35.62/4.98  --comb_sup_mult                         2
% 35.62/4.98  --comb_inst_mult                        10
% 35.62/4.98  
% 35.62/4.98  ------ Debug Options
% 35.62/4.98  
% 35.62/4.98  --dbg_backtrace                         false
% 35.62/4.98  --dbg_dump_prop_clauses                 false
% 35.62/4.98  --dbg_dump_prop_clauses_file            -
% 35.62/4.98  --dbg_out_stat                          false
% 35.62/4.98  
% 35.62/4.98  
% 35.62/4.98  
% 35.62/4.98  
% 35.62/4.98  ------ Proving...
% 35.62/4.98  
% 35.62/4.98  
% 35.62/4.98  % SZS status Theorem for theBenchmark.p
% 35.62/4.98  
% 35.62/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.62/4.98  
% 35.62/4.98  fof(f5,axiom,(
% 35.62/4.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f15,plain,(
% 35.62/4.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.62/4.98    inference(ennf_transformation,[],[f5])).
% 35.62/4.98  
% 35.62/4.98  fof(f16,plain,(
% 35.62/4.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.62/4.98    inference(flattening,[],[f15])).
% 35.62/4.98  
% 35.62/4.98  fof(f36,plain,(
% 35.62/4.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.62/4.98    inference(cnf_transformation,[],[f16])).
% 35.62/4.98  
% 35.62/4.98  fof(f9,axiom,(
% 35.62/4.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f20,plain,(
% 35.62/4.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.62/4.98    inference(ennf_transformation,[],[f9])).
% 35.62/4.98  
% 35.62/4.98  fof(f21,plain,(
% 35.62/4.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.62/4.98    inference(flattening,[],[f20])).
% 35.62/4.98  
% 35.62/4.98  fof(f41,plain,(
% 35.62/4.98    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.62/4.98    inference(cnf_transformation,[],[f21])).
% 35.62/4.98  
% 35.62/4.98  fof(f10,conjecture,(
% 35.62/4.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f11,negated_conjecture,(
% 35.62/4.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 35.62/4.98    inference(negated_conjecture,[],[f10])).
% 35.62/4.98  
% 35.62/4.98  fof(f22,plain,(
% 35.62/4.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.62/4.98    inference(ennf_transformation,[],[f11])).
% 35.62/4.98  
% 35.62/4.98  fof(f28,plain,(
% 35.62/4.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.62/4.98    introduced(choice_axiom,[])).
% 35.62/4.98  
% 35.62/4.98  fof(f27,plain,(
% 35.62/4.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.62/4.98    introduced(choice_axiom,[])).
% 35.62/4.98  
% 35.62/4.98  fof(f26,plain,(
% 35.62/4.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 35.62/4.98    introduced(choice_axiom,[])).
% 35.62/4.98  
% 35.62/4.98  fof(f29,plain,(
% 35.62/4.98    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 35.62/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28,f27,f26])).
% 35.62/4.98  
% 35.62/4.98  fof(f42,plain,(
% 35.62/4.98    l1_pre_topc(sK0)),
% 35.62/4.98    inference(cnf_transformation,[],[f29])).
% 35.62/4.98  
% 35.62/4.98  fof(f2,axiom,(
% 35.62/4.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f12,plain,(
% 35.62/4.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 35.62/4.98    inference(ennf_transformation,[],[f2])).
% 35.62/4.98  
% 35.62/4.98  fof(f33,plain,(
% 35.62/4.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 35.62/4.98    inference(cnf_transformation,[],[f12])).
% 35.62/4.98  
% 35.62/4.98  fof(f4,axiom,(
% 35.62/4.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f35,plain,(
% 35.62/4.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.62/4.98    inference(cnf_transformation,[],[f4])).
% 35.62/4.98  
% 35.62/4.98  fof(f7,axiom,(
% 35.62/4.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f25,plain,(
% 35.62/4.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.62/4.98    inference(nnf_transformation,[],[f7])).
% 35.62/4.98  
% 35.62/4.98  fof(f39,plain,(
% 35.62/4.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.62/4.98    inference(cnf_transformation,[],[f25])).
% 35.62/4.98  
% 35.62/4.98  fof(f3,axiom,(
% 35.62/4.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f13,plain,(
% 35.62/4.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 35.62/4.98    inference(ennf_transformation,[],[f3])).
% 35.62/4.98  
% 35.62/4.98  fof(f14,plain,(
% 35.62/4.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 35.62/4.98    inference(flattening,[],[f13])).
% 35.62/4.98  
% 35.62/4.98  fof(f34,plain,(
% 35.62/4.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 35.62/4.98    inference(cnf_transformation,[],[f14])).
% 35.62/4.98  
% 35.62/4.98  fof(f44,plain,(
% 35.62/4.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.62/4.98    inference(cnf_transformation,[],[f29])).
% 35.62/4.98  
% 35.62/4.98  fof(f38,plain,(
% 35.62/4.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.62/4.98    inference(cnf_transformation,[],[f25])).
% 35.62/4.98  
% 35.62/4.98  fof(f43,plain,(
% 35.62/4.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.62/4.98    inference(cnf_transformation,[],[f29])).
% 35.62/4.98  
% 35.62/4.98  fof(f6,axiom,(
% 35.62/4.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f17,plain,(
% 35.62/4.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.62/4.98    inference(ennf_transformation,[],[f6])).
% 35.62/4.98  
% 35.62/4.98  fof(f18,plain,(
% 35.62/4.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.62/4.98    inference(flattening,[],[f17])).
% 35.62/4.98  
% 35.62/4.98  fof(f37,plain,(
% 35.62/4.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.62/4.98    inference(cnf_transformation,[],[f18])).
% 35.62/4.98  
% 35.62/4.98  fof(f1,axiom,(
% 35.62/4.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f23,plain,(
% 35.62/4.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.62/4.98    inference(nnf_transformation,[],[f1])).
% 35.62/4.98  
% 35.62/4.98  fof(f24,plain,(
% 35.62/4.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.62/4.98    inference(flattening,[],[f23])).
% 35.62/4.98  
% 35.62/4.98  fof(f32,plain,(
% 35.62/4.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.62/4.98    inference(cnf_transformation,[],[f24])).
% 35.62/4.98  
% 35.62/4.98  fof(f30,plain,(
% 35.62/4.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.62/4.98    inference(cnf_transformation,[],[f24])).
% 35.62/4.98  
% 35.62/4.98  fof(f47,plain,(
% 35.62/4.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.62/4.98    inference(equality_resolution,[],[f30])).
% 35.62/4.98  
% 35.62/4.98  fof(f8,axiom,(
% 35.62/4.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 35.62/4.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.62/4.98  
% 35.62/4.98  fof(f19,plain,(
% 35.62/4.98    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.62/4.98    inference(ennf_transformation,[],[f8])).
% 35.62/4.98  
% 35.62/4.98  fof(f40,plain,(
% 35.62/4.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.62/4.98    inference(cnf_transformation,[],[f19])).
% 35.62/4.98  
% 35.62/4.98  fof(f45,plain,(
% 35.62/4.98    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 35.62/4.98    inference(cnf_transformation,[],[f29])).
% 35.62/4.98  
% 35.62/4.98  cnf(c_371,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.62/4.98      theory(equality) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_107022,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1)
% 35.62/4.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
% 35.62/4.98      | sK2 != X0 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_371]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_107664,plain,
% 35.62/4.98      ( ~ r1_tarski(sK2,X0)
% 35.62/4.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 35.62/4.98      | sK2 != sK2 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_107022]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_108803,plain,
% 35.62/4.98      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | ~ r1_tarski(sK2,k2_xboole_0(X0,X1))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,X1)
% 35.62/4.98      | sK2 != sK2 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_107664]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_115165,plain,
% 35.62/4.98      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | ~ r1_tarski(sK2,k2_xboole_0(X0,sK2))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,sK2)
% 35.62/4.98      | sK2 != sK2 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_108803]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_137307,plain,
% 35.62/4.98      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 35.62/4.98      | sK2 != sK2 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_115165]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_6,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1)
% 35.62/4.98      | ~ r1_tarski(X2,X1)
% 35.62/4.98      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 35.62/4.98      inference(cnf_transformation,[],[f36]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_108050,plain,
% 35.62/4.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X0,X1))
% 35.62/4.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(X0,X1))
% 35.62/4.98      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_6]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_112244,plain,
% 35.62/4.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
% 35.62/4.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
% 35.62/4.98      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_108050]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_134655,plain,
% 35.62/4.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_112244]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_106124,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1)
% 35.62/4.98      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 35.62/4.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_371]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_106173,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
% 35.62/4.98      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 35.62/4.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_106124]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_107377,plain,
% 35.62/4.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 35.62/4.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,X1) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_106173]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_134121,plain,
% 35.62/4.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 35.62/4.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_107377]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_107038,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1)
% 35.62/4.98      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
% 35.62/4.98      | sK1 != X0 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_371]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_107675,plain,
% 35.62/4.98      ( ~ r1_tarski(sK1,X0)
% 35.62/4.98      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 35.62/4.98      | sK1 != sK1 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_107038]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_108818,plain,
% 35.62/4.98      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | ~ r1_tarski(sK1,k2_xboole_0(X0,X1))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(X0,X1)
% 35.62/4.98      | sK1 != sK1 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_107675]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_111330,plain,
% 35.62/4.98      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | ~ r1_tarski(sK1,k2_xboole_0(sK1,X0))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,X0)
% 35.62/4.98      | sK1 != sK1 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_108818]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_118826,plain,
% 35.62/4.98      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 35.62/4.98      | sK1 != sK1 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_111330]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_11,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.62/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.62/4.98      | ~ r1_tarski(X0,X2)
% 35.62/4.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 35.62/4.98      | ~ l1_pre_topc(X1) ),
% 35.62/4.98      inference(cnf_transformation,[],[f41]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_15,negated_conjecture,
% 35.62/4.98      ( l1_pre_topc(sK0) ),
% 35.62/4.98      inference(cnf_transformation,[],[f42]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_203,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.62/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.62/4.98      | ~ r1_tarski(X0,X2)
% 35.62/4.98      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 35.62/4.98      | sK0 != X1 ),
% 35.62/4.98      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_204,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ r1_tarski(X1,X0)
% 35.62/4.98      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 35.62/4.98      inference(unflattening,[status(thm)],[c_203]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_8976,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 35.62/4.98      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_204]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_59558,plain,
% 35.62/4.98      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_8976]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_59555,plain,
% 35.62/4.98      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.62/4.98      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_8976]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_3,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 35.62/4.98      inference(cnf_transformation,[],[f33]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_5575,plain,
% 35.62/4.98      ( r1_tarski(X0,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(X0,sK2) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_3]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_40940,plain,
% 35.62/4.98      ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(sK2,sK2) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_5575]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_374,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.62/4.98      theory(equality) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_746,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,X1)
% 35.62/4.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | X2 != X0
% 35.62/4.98      | k1_zfmisc_1(u1_struct_0(sK0)) != X1 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_374]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_970,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | X1 != X0
% 35.62/4.98      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_746]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_5098,plain,
% 35.62/4.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | X0 != k2_xboole_0(sK1,sK2)
% 35.62/4.98      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_970]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_40404,plain,
% 35.62/4.98      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 35.62/4.98      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_5098]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_5,plain,
% 35.62/4.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 35.62/4.98      inference(cnf_transformation,[],[f35]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_15581,plain,
% 35.62/4.98      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_5]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_8,plain,
% 35.62/4.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.62/4.98      inference(cnf_transformation,[],[f39]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_741,plain,
% 35.62/4.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_8]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_824,plain,
% 35.62/4.98      ( m1_subset_1(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_741]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_3748,plain,
% 35.62/4.98      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | ~ r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_824]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1032,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 35.62/4.98      | r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_6]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1888,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 35.62/4.98      | r1_tarski(k2_xboole_0(sK1,X0),u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_1032]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_2309,plain,
% 35.62/4.98      ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_1888]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_4,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 35.62/4.98      inference(cnf_transformation,[],[f34]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_821,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1)
% 35.62/4.98      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 35.62/4.98      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_4]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1404,plain,
% 35.62/4.98      ( r1_tarski(X0,u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(X0,sK1)
% 35.62/4.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_821]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_2242,plain,
% 35.62/4.98      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 35.62/4.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_1404]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1398,plain,
% 35.62/4.98      ( r1_tarski(X0,u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(X0,sK2)
% 35.62/4.98      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_821]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_2195,plain,
% 35.62/4.98      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 35.62/4.98      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_1398]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_13,negated_conjecture,
% 35.62/4.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.62/4.98      inference(cnf_transformation,[],[f44]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_693,plain,
% 35.62/4.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.62/4.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_9,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.62/4.98      inference(cnf_transformation,[],[f38]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_695,plain,
% 35.62/4.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.62/4.98      | r1_tarski(X0,X1) = iProver_top ),
% 35.62/4.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1450,plain,
% 35.62/4.98      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 35.62/4.98      inference(superposition,[status(thm)],[c_693,c_695]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_14,negated_conjecture,
% 35.62/4.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.62/4.98      inference(cnf_transformation,[],[f43]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_692,plain,
% 35.62/4.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.62/4.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1451,plain,
% 35.62/4.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 35.62/4.98      inference(superposition,[status(thm)],[c_692,c_695]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_7,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.62/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.62/4.98      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 35.62/4.98      inference(cnf_transformation,[],[f37]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_118,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.62/4.98      inference(prop_impl,[status(thm)],[c_8]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_119,plain,
% 35.62/4.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.62/4.98      inference(renaming,[status(thm)],[c_118]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_145,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.62/4.98      | ~ r1_tarski(X2,X1)
% 35.62/4.98      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 35.62/4.98      inference(bin_hyper_res,[status(thm)],[c_7,c_119]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_289,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.62/4.98      inference(prop_impl,[status(thm)],[c_8]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_290,plain,
% 35.62/4.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.62/4.98      inference(renaming,[status(thm)],[c_289]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_314,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1)
% 35.62/4.98      | ~ r1_tarski(X2,X1)
% 35.62/4.98      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 35.62/4.98      inference(bin_hyper_res,[status(thm)],[c_145,c_290]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_689,plain,
% 35.62/4.98      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 35.62/4.98      | r1_tarski(X1,X0) != iProver_top
% 35.62/4.98      | r1_tarski(X2,X0) != iProver_top ),
% 35.62/4.98      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1637,plain,
% 35.62/4.98      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 35.62/4.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 35.62/4.98      inference(superposition,[status(thm)],[c_1451,c_689]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1816,plain,
% 35.62/4.98      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 35.62/4.98      inference(superposition,[status(thm)],[c_1450,c_1637]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1552,plain,
% 35.62/4.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 35.62/4.98      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 35.62/4.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_314]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_0,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.62/4.98      inference(cnf_transformation,[],[f32]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1140,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_0]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1539,plain,
% 35.62/4.98      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_1140]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1123,plain,
% 35.62/4.98      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_0]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1524,plain,
% 35.62/4.98      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_1123]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_369,plain,( X0 = X0 ),theory(equality) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1285,plain,
% 35.62/4.98      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_369]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_813,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_9]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1166,plain,
% 35.62/4.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_813]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1163,plain,
% 35.62/4.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_813]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_2,plain,
% 35.62/4.98      ( r1_tarski(X0,X0) ),
% 35.62/4.98      inference(cnf_transformation,[],[f47]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1039,plain,
% 35.62/4.98      ( r1_tarski(sK1,sK1) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_2]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_1017,plain,
% 35.62/4.98      ( r1_tarski(sK2,sK2) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_2]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_908,plain,
% 35.62/4.98      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_369]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_10,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.62/4.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 35.62/4.98      | ~ l1_pre_topc(X1) ),
% 35.62/4.98      inference(cnf_transformation,[],[f40]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_221,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.62/4.98      | r1_tarski(k1_tops_1(X1,X0),X0)
% 35.62/4.98      | sK0 != X1 ),
% 35.62/4.98      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_222,plain,
% 35.62/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 35.62/4.98      inference(unflattening,[status(thm)],[c_221]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_738,plain,
% 35.62/4.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_222]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_735,plain,
% 35.62/4.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.62/4.98      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 35.62/4.98      inference(instantiation,[status(thm)],[c_222]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(c_12,negated_conjecture,
% 35.62/4.98      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 35.62/4.98      inference(cnf_transformation,[],[f45]) ).
% 35.62/4.98  
% 35.62/4.98  cnf(contradiction,plain,
% 35.62/4.98      ( $false ),
% 35.62/4.98      inference(minisat,
% 35.62/4.98                [status(thm)],
% 35.62/4.98                [c_137307,c_134655,c_134121,c_118826,c_59558,c_59555,
% 35.62/4.98                 c_40940,c_40404,c_15581,c_3748,c_2309,c_2242,c_2195,
% 35.62/4.98                 c_1816,c_1552,c_1539,c_1524,c_1285,c_1166,c_1163,c_1039,
% 35.62/4.98                 c_1017,c_908,c_738,c_735,c_12,c_13,c_14]) ).
% 35.62/4.98  
% 35.62/4.98  
% 35.62/4.98  % SZS output end CNFRefutation for theBenchmark.p
% 35.62/4.98  
% 35.62/4.98  ------                               Statistics
% 35.62/4.98  
% 35.62/4.98  ------ General
% 35.62/4.98  
% 35.62/4.98  abstr_ref_over_cycles:                  0
% 35.62/4.98  abstr_ref_under_cycles:                 0
% 35.62/4.98  gc_basic_clause_elim:                   0
% 35.62/4.98  forced_gc_time:                         0
% 35.62/4.98  parsing_time:                           0.008
% 35.62/4.98  unif_index_cands_time:                  0.
% 35.62/4.98  unif_index_add_time:                    0.
% 35.62/4.98  orderings_time:                         0.
% 35.62/4.98  out_proof_time:                         0.017
% 35.62/4.98  total_time:                             4.182
% 35.62/4.98  num_of_symbols:                         42
% 35.62/4.98  num_of_terms:                           122216
% 35.62/4.98  
% 35.62/4.98  ------ Preprocessing
% 35.62/4.98  
% 35.62/4.98  num_of_splits:                          0
% 35.62/4.98  num_of_split_atoms:                     0
% 35.62/4.98  num_of_reused_defs:                     0
% 35.62/4.98  num_eq_ax_congr_red:                    6
% 35.62/4.98  num_of_sem_filtered_clauses:            1
% 35.62/4.98  num_of_subtypes:                        0
% 35.62/4.98  monotx_restored_types:                  0
% 35.62/4.98  sat_num_of_epr_types:                   0
% 35.62/4.98  sat_num_of_non_cyclic_types:            0
% 35.62/4.98  sat_guarded_non_collapsed_types:        0
% 35.62/4.98  num_pure_diseq_elim:                    0
% 35.62/4.98  simp_replaced_by:                       0
% 35.62/4.98  res_preprocessed:                       74
% 35.62/4.98  prep_upred:                             0
% 35.62/4.98  prep_unflattend:                        2
% 35.62/4.98  smt_new_axioms:                         0
% 35.62/4.98  pred_elim_cands:                        2
% 35.62/4.98  pred_elim:                              1
% 35.62/4.98  pred_elim_cl:                           1
% 35.62/4.98  pred_elim_cycles:                       3
% 35.62/4.98  merged_defs:                            8
% 35.62/4.98  merged_defs_ncl:                        0
% 35.62/4.98  bin_hyper_res:                          10
% 35.62/4.98  prep_cycles:                            4
% 35.62/4.98  pred_elim_time:                         0.001
% 35.62/4.98  splitting_time:                         0.
% 35.62/4.98  sem_filter_time:                        0.
% 35.62/4.98  monotx_time:                            0.
% 35.62/4.98  subtype_inf_time:                       0.
% 35.62/4.98  
% 35.62/4.98  ------ Problem properties
% 35.62/4.98  
% 35.62/4.98  clauses:                                14
% 35.62/4.98  conjectures:                            3
% 35.62/4.98  epr:                                    3
% 35.62/4.98  horn:                                   14
% 35.62/4.98  ground:                                 3
% 35.62/4.98  unary:                                  5
% 35.62/4.98  binary:                                 4
% 35.62/4.98  lits:                                   29
% 35.62/4.98  lits_eq:                                2
% 35.62/4.98  fd_pure:                                0
% 35.62/4.98  fd_pseudo:                              0
% 35.62/4.98  fd_cond:                                0
% 35.62/4.98  fd_pseudo_cond:                         1
% 35.62/4.98  ac_symbols:                             0
% 35.62/4.98  
% 35.62/4.98  ------ Propositional Solver
% 35.62/4.98  
% 35.62/4.98  prop_solver_calls:                      63
% 35.62/4.98  prop_fast_solver_calls:                 2836
% 35.62/4.98  smt_solver_calls:                       0
% 35.62/4.98  smt_fast_solver_calls:                  0
% 35.62/4.98  prop_num_of_clauses:                    62040
% 35.62/4.98  prop_preprocess_simplified:             62516
% 35.62/4.98  prop_fo_subsumed:                       155
% 35.62/4.98  prop_solver_time:                       0.
% 35.62/4.98  smt_solver_time:                        0.
% 35.62/4.98  smt_fast_solver_time:                   0.
% 35.62/4.98  prop_fast_solver_time:                  0.
% 35.62/4.98  prop_unsat_core_time:                   0.006
% 35.62/4.98  
% 35.62/4.98  ------ QBF
% 35.62/4.98  
% 35.62/4.98  qbf_q_res:                              0
% 35.62/4.98  qbf_num_tautologies:                    0
% 35.62/4.98  qbf_prep_cycles:                        0
% 35.62/4.98  
% 35.62/4.98  ------ BMC1
% 35.62/4.98  
% 35.62/4.98  bmc1_current_bound:                     -1
% 35.62/4.98  bmc1_last_solved_bound:                 -1
% 35.62/4.98  bmc1_unsat_core_size:                   -1
% 35.62/4.98  bmc1_unsat_core_parents_size:           -1
% 35.62/4.98  bmc1_merge_next_fun:                    0
% 35.62/4.98  bmc1_unsat_core_clauses_time:           0.
% 35.62/4.98  
% 35.62/4.98  ------ Instantiation
% 35.62/4.98  
% 35.62/4.98  inst_num_of_clauses:                    2325
% 35.62/4.98  inst_num_in_passive:                    355
% 35.62/4.98  inst_num_in_active:                     3195
% 35.62/4.98  inst_num_in_unprocessed:                1158
% 35.62/4.98  inst_num_of_loops:                      3862
% 35.62/4.98  inst_num_of_learning_restarts:          1
% 35.62/4.98  inst_num_moves_active_passive:          663
% 35.62/4.98  inst_lit_activity:                      0
% 35.62/4.98  inst_lit_activity_moves:                6
% 35.62/4.98  inst_num_tautologies:                   0
% 35.62/4.98  inst_num_prop_implied:                  0
% 35.62/4.98  inst_num_existing_simplified:           0
% 35.62/4.98  inst_num_eq_res_simplified:             0
% 35.62/4.98  inst_num_child_elim:                    0
% 35.62/4.98  inst_num_of_dismatching_blockings:      26910
% 35.62/4.98  inst_num_of_non_proper_insts:           14576
% 35.62/4.98  inst_num_of_duplicates:                 0
% 35.62/4.98  inst_inst_num_from_inst_to_res:         0
% 35.62/4.98  inst_dismatching_checking_time:         0.
% 35.62/4.98  
% 35.62/4.98  ------ Resolution
% 35.62/4.98  
% 35.62/4.98  res_num_of_clauses:                     22
% 35.62/4.98  res_num_in_passive:                     22
% 35.62/4.98  res_num_in_active:                      0
% 35.62/4.98  res_num_of_loops:                       78
% 35.62/4.98  res_forward_subset_subsumed:            559
% 35.62/4.98  res_backward_subset_subsumed:           4
% 35.62/4.98  res_forward_subsumed:                   0
% 35.62/4.98  res_backward_subsumed:                  0
% 35.62/4.98  res_forward_subsumption_resolution:     0
% 35.62/4.98  res_backward_subsumption_resolution:    0
% 35.62/4.98  res_clause_to_clause_subsumption:       206326
% 35.62/4.98  res_orphan_elimination:                 0
% 35.62/4.98  res_tautology_del:                      700
% 35.62/4.98  res_num_eq_res_simplified:              0
% 35.62/4.98  res_num_sel_changes:                    0
% 35.62/4.98  res_moves_from_active_to_pass:          0
% 35.62/4.98  
% 35.62/4.98  ------ Superposition
% 35.62/4.98  
% 35.62/4.98  sup_time_total:                         0.
% 35.62/4.98  sup_time_generating:                    0.
% 35.62/4.98  sup_time_sim_full:                      0.
% 35.62/4.98  sup_time_sim_immed:                     0.
% 35.62/4.98  
% 35.62/4.98  sup_num_of_clauses:                     10568
% 35.62/4.98  sup_num_in_active:                      674
% 35.62/4.98  sup_num_in_passive:                     9894
% 35.62/4.98  sup_num_of_loops:                       772
% 35.62/4.98  sup_fw_superposition:                   11692
% 35.62/4.98  sup_bw_superposition:                   9544
% 35.62/4.98  sup_immediate_simplified:               5367
% 35.62/4.98  sup_given_eliminated:                   0
% 35.62/4.98  comparisons_done:                       0
% 35.62/4.98  comparisons_avoided:                    0
% 35.62/4.98  
% 35.62/4.98  ------ Simplifications
% 35.62/4.98  
% 35.62/4.98  
% 35.62/4.98  sim_fw_subset_subsumed:                 1159
% 35.62/4.98  sim_bw_subset_subsumed:                 228
% 35.62/4.98  sim_fw_subsumed:                        1960
% 35.62/4.98  sim_bw_subsumed:                        314
% 35.62/4.98  sim_fw_subsumption_res:                 0
% 35.62/4.98  sim_bw_subsumption_res:                 0
% 35.62/4.98  sim_tautology_del:                      225
% 35.62/4.98  sim_eq_tautology_del:                   521
% 35.62/4.98  sim_eq_res_simp:                        0
% 35.62/4.98  sim_fw_demodulated:                     1464
% 35.62/4.98  sim_bw_demodulated:                     96
% 35.62/4.98  sim_light_normalised:                   1115
% 35.62/4.98  sim_joinable_taut:                      0
% 35.62/4.98  sim_joinable_simp:                      0
% 35.62/4.98  sim_ac_normalised:                      0
% 35.62/4.98  sim_smt_subsumption:                    0
% 35.62/4.98  
%------------------------------------------------------------------------------
