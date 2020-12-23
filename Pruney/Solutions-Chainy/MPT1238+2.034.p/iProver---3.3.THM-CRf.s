%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:51 EST 2020

% Result     : Theorem 31.38s
% Output     : CNFRefutation 31.38s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 514 expanded)
%              Number of clauses        :  114 ( 215 expanded)
%              Number of leaves         :   17 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  407 (1592 expanded)
%              Number of equality atoms :  121 ( 282 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f46,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_76170,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_110084,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_76170])).

cnf(c_392,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_75888,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_75902,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_75888])).

cnf(c_75929,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0,X1)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_75902])).

cnf(c_109581,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_75929])).

cnf(c_75932,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | X2 != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_76501,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
    | r1_tarski(X3,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | X3 != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_75932])).

cnf(c_78472,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,k2_xboole_0(sK1,sK2)))
    | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | X2 != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_76501])).

cnf(c_82353,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | X0 != k1_tops_1(sK0,X1)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_78472])).

cnf(c_88076,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,X0) != k1_tops_1(sK0,X0)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_82353])).

cnf(c_104141,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_88076])).

cnf(c_77430,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X2,X3))
    | k1_tops_1(X2,X3) != X1
    | k1_tops_1(sK0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_80370,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X1,X2))
    | k1_tops_1(X1,X2) != X0
    | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_77430])).

cnf(c_87932,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X0,X1))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(X0,X1) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_80370])).

cnf(c_104127,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_87932])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15073,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_75065,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_15073])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16602,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_50791,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_16602])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_730,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_733,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1422,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_733])).

cnf(c_735,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_736,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_741,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2228,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_741])).

cnf(c_8146,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_735,c_2228])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_47,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15914,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8146,c_47])).

cnf(c_15924,plain,
    ( k2_xboole_0(u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1422,c_15914])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_738,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_728,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_969,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_728])).

cnf(c_15928,plain,
    ( k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_969,c_15914])).

cnf(c_739,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17409,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_15928,c_739])).

cnf(c_18661,plain,
    ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_17409])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_737,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19002,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18661,c_737])).

cnf(c_19032,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15924,c_19002])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_731,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1421,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_733])).

cnf(c_15923,plain,
    ( k2_xboole_0(u1_struct_0(sK0),sK2) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1421,c_15914])).

cnf(c_968,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_728])).

cnf(c_15927,plain,
    ( k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_968,c_15914])).

cnf(c_17023,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_15927,c_739])).

cnf(c_18482,plain,
    ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK2),X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_17023])).

cnf(c_18537,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(X0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18482,c_737])).

cnf(c_18567,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15923,c_18537])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_8036,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_15214,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8036])).

cnf(c_15211,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8036])).

cnf(c_4309,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | X0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_10995,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4309])).

cnf(c_2537,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
    | X0 = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6339,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,sK2) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_2537])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_776,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_925,plain,
    ( m1_subset_1(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_4295,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_396,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_1732,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_3572,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_3573,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3572])).

cnf(c_1325,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2107,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(k2_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_2576,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_127,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_128,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_127])).

cnf(c_155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_128])).

cnf(c_306,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_307,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_155,c_307])).

cnf(c_727,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1652,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_727])).

cnf(c_1826,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1421,c_1652])).

cnf(c_1625,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_1626,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_912,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1153,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_1150,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_390,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_956,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_908,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_901,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_846,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_786,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_820,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_52,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_48,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_110084,c_109581,c_104141,c_104127,c_75065,c_50791,c_19032,c_18567,c_15214,c_15211,c_10995,c_6339,c_4295,c_3573,c_2576,c_1826,c_1626,c_1153,c_1150,c_956,c_908,c_901,c_846,c_820,c_52,c_48,c_13,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 12:09:50 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 31.38/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.38/4.50  
% 31.38/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.38/4.50  
% 31.38/4.50  ------  iProver source info
% 31.38/4.50  
% 31.38/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.38/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.38/4.50  git: non_committed_changes: false
% 31.38/4.50  git: last_make_outside_of_git: false
% 31.38/4.50  
% 31.38/4.50  ------ 
% 31.38/4.50  
% 31.38/4.50  ------ Input Options
% 31.38/4.50  
% 31.38/4.50  --out_options                           all
% 31.38/4.50  --tptp_safe_out                         true
% 31.38/4.50  --problem_path                          ""
% 31.38/4.50  --include_path                          ""
% 31.38/4.50  --clausifier                            res/vclausify_rel
% 31.38/4.50  --clausifier_options                    ""
% 31.38/4.50  --stdin                                 false
% 31.38/4.50  --stats_out                             all
% 31.38/4.50  
% 31.38/4.50  ------ General Options
% 31.38/4.50  
% 31.38/4.50  --fof                                   false
% 31.38/4.50  --time_out_real                         305.
% 31.38/4.50  --time_out_virtual                      -1.
% 31.38/4.50  --symbol_type_check                     false
% 31.38/4.50  --clausify_out                          false
% 31.38/4.50  --sig_cnt_out                           false
% 31.38/4.50  --trig_cnt_out                          false
% 31.38/4.50  --trig_cnt_out_tolerance                1.
% 31.38/4.50  --trig_cnt_out_sk_spl                   false
% 31.38/4.50  --abstr_cl_out                          false
% 31.38/4.50  
% 31.38/4.50  ------ Global Options
% 31.38/4.50  
% 31.38/4.50  --schedule                              default
% 31.38/4.50  --add_important_lit                     false
% 31.38/4.50  --prop_solver_per_cl                    1000
% 31.38/4.50  --min_unsat_core                        false
% 31.38/4.50  --soft_assumptions                      false
% 31.38/4.50  --soft_lemma_size                       3
% 31.38/4.50  --prop_impl_unit_size                   0
% 31.38/4.50  --prop_impl_unit                        []
% 31.38/4.50  --share_sel_clauses                     true
% 31.38/4.50  --reset_solvers                         false
% 31.38/4.50  --bc_imp_inh                            [conj_cone]
% 31.38/4.50  --conj_cone_tolerance                   3.
% 31.38/4.50  --extra_neg_conj                        none
% 31.38/4.50  --large_theory_mode                     true
% 31.38/4.50  --prolific_symb_bound                   200
% 31.38/4.50  --lt_threshold                          2000
% 31.38/4.50  --clause_weak_htbl                      true
% 31.38/4.50  --gc_record_bc_elim                     false
% 31.38/4.50  
% 31.38/4.50  ------ Preprocessing Options
% 31.38/4.50  
% 31.38/4.50  --preprocessing_flag                    true
% 31.38/4.50  --time_out_prep_mult                    0.1
% 31.38/4.50  --splitting_mode                        input
% 31.38/4.50  --splitting_grd                         true
% 31.38/4.50  --splitting_cvd                         false
% 31.38/4.50  --splitting_cvd_svl                     false
% 31.38/4.50  --splitting_nvd                         32
% 31.38/4.50  --sub_typing                            true
% 31.38/4.50  --prep_gs_sim                           true
% 31.38/4.50  --prep_unflatten                        true
% 31.38/4.50  --prep_res_sim                          true
% 31.38/4.50  --prep_upred                            true
% 31.38/4.50  --prep_sem_filter                       exhaustive
% 31.38/4.50  --prep_sem_filter_out                   false
% 31.38/4.50  --pred_elim                             true
% 31.38/4.50  --res_sim_input                         true
% 31.38/4.50  --eq_ax_congr_red                       true
% 31.38/4.50  --pure_diseq_elim                       true
% 31.38/4.50  --brand_transform                       false
% 31.38/4.50  --non_eq_to_eq                          false
% 31.38/4.50  --prep_def_merge                        true
% 31.38/4.50  --prep_def_merge_prop_impl              false
% 31.38/4.50  --prep_def_merge_mbd                    true
% 31.38/4.50  --prep_def_merge_tr_red                 false
% 31.38/4.50  --prep_def_merge_tr_cl                  false
% 31.38/4.50  --smt_preprocessing                     true
% 31.38/4.50  --smt_ac_axioms                         fast
% 31.38/4.50  --preprocessed_out                      false
% 31.38/4.50  --preprocessed_stats                    false
% 31.38/4.50  
% 31.38/4.50  ------ Abstraction refinement Options
% 31.38/4.50  
% 31.38/4.50  --abstr_ref                             []
% 31.38/4.50  --abstr_ref_prep                        false
% 31.38/4.50  --abstr_ref_until_sat                   false
% 31.38/4.50  --abstr_ref_sig_restrict                funpre
% 31.38/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.38/4.50  --abstr_ref_under                       []
% 31.38/4.50  
% 31.38/4.50  ------ SAT Options
% 31.38/4.50  
% 31.38/4.50  --sat_mode                              false
% 31.38/4.50  --sat_fm_restart_options                ""
% 31.38/4.50  --sat_gr_def                            false
% 31.38/4.50  --sat_epr_types                         true
% 31.38/4.50  --sat_non_cyclic_types                  false
% 31.38/4.50  --sat_finite_models                     false
% 31.38/4.50  --sat_fm_lemmas                         false
% 31.38/4.50  --sat_fm_prep                           false
% 31.38/4.50  --sat_fm_uc_incr                        true
% 31.38/4.50  --sat_out_model                         small
% 31.38/4.50  --sat_out_clauses                       false
% 31.38/4.50  
% 31.38/4.50  ------ QBF Options
% 31.38/4.50  
% 31.38/4.50  --qbf_mode                              false
% 31.38/4.50  --qbf_elim_univ                         false
% 31.38/4.50  --qbf_dom_inst                          none
% 31.38/4.50  --qbf_dom_pre_inst                      false
% 31.38/4.50  --qbf_sk_in                             false
% 31.38/4.50  --qbf_pred_elim                         true
% 31.38/4.50  --qbf_split                             512
% 31.38/4.50  
% 31.38/4.50  ------ BMC1 Options
% 31.38/4.50  
% 31.38/4.50  --bmc1_incremental                      false
% 31.38/4.50  --bmc1_axioms                           reachable_all
% 31.38/4.50  --bmc1_min_bound                        0
% 31.38/4.50  --bmc1_max_bound                        -1
% 31.38/4.50  --bmc1_max_bound_default                -1
% 31.38/4.50  --bmc1_symbol_reachability              true
% 31.38/4.50  --bmc1_property_lemmas                  false
% 31.38/4.50  --bmc1_k_induction                      false
% 31.38/4.50  --bmc1_non_equiv_states                 false
% 31.38/4.50  --bmc1_deadlock                         false
% 31.38/4.50  --bmc1_ucm                              false
% 31.38/4.50  --bmc1_add_unsat_core                   none
% 31.38/4.50  --bmc1_unsat_core_children              false
% 31.38/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.38/4.50  --bmc1_out_stat                         full
% 31.38/4.50  --bmc1_ground_init                      false
% 31.38/4.50  --bmc1_pre_inst_next_state              false
% 31.38/4.50  --bmc1_pre_inst_state                   false
% 31.38/4.50  --bmc1_pre_inst_reach_state             false
% 31.38/4.50  --bmc1_out_unsat_core                   false
% 31.38/4.50  --bmc1_aig_witness_out                  false
% 31.38/4.50  --bmc1_verbose                          false
% 31.38/4.50  --bmc1_dump_clauses_tptp                false
% 31.38/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.38/4.50  --bmc1_dump_file                        -
% 31.38/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.38/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.38/4.50  --bmc1_ucm_extend_mode                  1
% 31.38/4.50  --bmc1_ucm_init_mode                    2
% 31.38/4.50  --bmc1_ucm_cone_mode                    none
% 31.38/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.38/4.50  --bmc1_ucm_relax_model                  4
% 31.38/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.38/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.38/4.50  --bmc1_ucm_layered_model                none
% 31.38/4.50  --bmc1_ucm_max_lemma_size               10
% 31.38/4.50  
% 31.38/4.50  ------ AIG Options
% 31.38/4.50  
% 31.38/4.50  --aig_mode                              false
% 31.38/4.50  
% 31.38/4.50  ------ Instantiation Options
% 31.38/4.50  
% 31.38/4.50  --instantiation_flag                    true
% 31.38/4.50  --inst_sos_flag                         true
% 31.38/4.50  --inst_sos_phase                        true
% 31.38/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.38/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.38/4.50  --inst_lit_sel_side                     num_symb
% 31.38/4.50  --inst_solver_per_active                1400
% 31.38/4.50  --inst_solver_calls_frac                1.
% 31.38/4.50  --inst_passive_queue_type               priority_queues
% 31.38/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.38/4.50  --inst_passive_queues_freq              [25;2]
% 31.38/4.50  --inst_dismatching                      true
% 31.38/4.50  --inst_eager_unprocessed_to_passive     true
% 31.38/4.50  --inst_prop_sim_given                   true
% 31.38/4.50  --inst_prop_sim_new                     false
% 31.38/4.50  --inst_subs_new                         false
% 31.38/4.50  --inst_eq_res_simp                      false
% 31.38/4.50  --inst_subs_given                       false
% 31.38/4.50  --inst_orphan_elimination               true
% 31.38/4.50  --inst_learning_loop_flag               true
% 31.38/4.50  --inst_learning_start                   3000
% 31.38/4.50  --inst_learning_factor                  2
% 31.38/4.50  --inst_start_prop_sim_after_learn       3
% 31.38/4.50  --inst_sel_renew                        solver
% 31.38/4.50  --inst_lit_activity_flag                true
% 31.38/4.50  --inst_restr_to_given                   false
% 31.38/4.50  --inst_activity_threshold               500
% 31.38/4.50  --inst_out_proof                        true
% 31.38/4.50  
% 31.38/4.50  ------ Resolution Options
% 31.38/4.50  
% 31.38/4.50  --resolution_flag                       true
% 31.38/4.50  --res_lit_sel                           adaptive
% 31.38/4.50  --res_lit_sel_side                      none
% 31.38/4.50  --res_ordering                          kbo
% 31.38/4.50  --res_to_prop_solver                    active
% 31.38/4.50  --res_prop_simpl_new                    false
% 31.38/4.50  --res_prop_simpl_given                  true
% 31.38/4.50  --res_passive_queue_type                priority_queues
% 31.38/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.38/4.50  --res_passive_queues_freq               [15;5]
% 31.38/4.50  --res_forward_subs                      full
% 31.38/4.50  --res_backward_subs                     full
% 31.38/4.50  --res_forward_subs_resolution           true
% 31.38/4.50  --res_backward_subs_resolution          true
% 31.38/4.50  --res_orphan_elimination                true
% 31.38/4.50  --res_time_limit                        2.
% 31.38/4.50  --res_out_proof                         true
% 31.38/4.50  
% 31.38/4.50  ------ Superposition Options
% 31.38/4.50  
% 31.38/4.50  --superposition_flag                    true
% 31.38/4.50  --sup_passive_queue_type                priority_queues
% 31.38/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.38/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.38/4.50  --demod_completeness_check              fast
% 31.38/4.50  --demod_use_ground                      true
% 31.38/4.50  --sup_to_prop_solver                    passive
% 31.38/4.50  --sup_prop_simpl_new                    true
% 31.38/4.50  --sup_prop_simpl_given                  true
% 31.38/4.50  --sup_fun_splitting                     true
% 31.38/4.50  --sup_smt_interval                      50000
% 31.38/4.50  
% 31.38/4.50  ------ Superposition Simplification Setup
% 31.38/4.50  
% 31.38/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.38/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.38/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.38/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.38/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.38/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.38/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.38/4.50  --sup_immed_triv                        [TrivRules]
% 31.38/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.38/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.38/4.50  --sup_immed_bw_main                     []
% 31.38/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.38/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.38/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.38/4.50  --sup_input_bw                          []
% 31.38/4.50  
% 31.38/4.50  ------ Combination Options
% 31.38/4.50  
% 31.38/4.50  --comb_res_mult                         3
% 31.38/4.50  --comb_sup_mult                         2
% 31.38/4.50  --comb_inst_mult                        10
% 31.38/4.50  
% 31.38/4.50  ------ Debug Options
% 31.38/4.50  
% 31.38/4.50  --dbg_backtrace                         false
% 31.38/4.50  --dbg_dump_prop_clauses                 false
% 31.38/4.50  --dbg_dump_prop_clauses_file            -
% 31.38/4.50  --dbg_out_stat                          false
% 31.38/4.50  ------ Parsing...
% 31.38/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.38/4.50  
% 31.38/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.38/4.50  
% 31.38/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.38/4.50  
% 31.38/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.38/4.50  ------ Proving...
% 31.38/4.50  ------ Problem Properties 
% 31.38/4.50  
% 31.38/4.50  
% 31.38/4.50  clauses                                 15
% 31.38/4.50  conjectures                             3
% 31.38/4.50  EPR                                     2
% 31.38/4.50  Horn                                    15
% 31.38/4.50  unary                                   6
% 31.38/4.50  binary                                  5
% 31.38/4.50  lits                                    29
% 31.38/4.50  lits eq                                 2
% 31.38/4.50  fd_pure                                 0
% 31.38/4.50  fd_pseudo                               0
% 31.38/4.50  fd_cond                                 0
% 31.38/4.50  fd_pseudo_cond                          1
% 31.38/4.50  AC symbols                              0
% 31.38/4.50  
% 31.38/4.50  ------ Schedule dynamic 5 is on 
% 31.38/4.50  
% 31.38/4.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.38/4.50  
% 31.38/4.50  
% 31.38/4.50  ------ 
% 31.38/4.50  Current options:
% 31.38/4.50  ------ 
% 31.38/4.50  
% 31.38/4.50  ------ Input Options
% 31.38/4.50  
% 31.38/4.50  --out_options                           all
% 31.38/4.50  --tptp_safe_out                         true
% 31.38/4.50  --problem_path                          ""
% 31.38/4.50  --include_path                          ""
% 31.38/4.50  --clausifier                            res/vclausify_rel
% 31.38/4.50  --clausifier_options                    ""
% 31.38/4.50  --stdin                                 false
% 31.38/4.50  --stats_out                             all
% 31.38/4.50  
% 31.38/4.50  ------ General Options
% 31.38/4.50  
% 31.38/4.50  --fof                                   false
% 31.38/4.50  --time_out_real                         305.
% 31.38/4.50  --time_out_virtual                      -1.
% 31.38/4.50  --symbol_type_check                     false
% 31.38/4.50  --clausify_out                          false
% 31.38/4.50  --sig_cnt_out                           false
% 31.38/4.50  --trig_cnt_out                          false
% 31.38/4.50  --trig_cnt_out_tolerance                1.
% 31.38/4.50  --trig_cnt_out_sk_spl                   false
% 31.38/4.50  --abstr_cl_out                          false
% 31.38/4.50  
% 31.38/4.50  ------ Global Options
% 31.38/4.50  
% 31.38/4.50  --schedule                              default
% 31.38/4.50  --add_important_lit                     false
% 31.38/4.50  --prop_solver_per_cl                    1000
% 31.38/4.50  --min_unsat_core                        false
% 31.38/4.50  --soft_assumptions                      false
% 31.38/4.50  --soft_lemma_size                       3
% 31.38/4.50  --prop_impl_unit_size                   0
% 31.38/4.50  --prop_impl_unit                        []
% 31.38/4.50  --share_sel_clauses                     true
% 31.38/4.50  --reset_solvers                         false
% 31.38/4.50  --bc_imp_inh                            [conj_cone]
% 31.38/4.50  --conj_cone_tolerance                   3.
% 31.38/4.50  --extra_neg_conj                        none
% 31.38/4.50  --large_theory_mode                     true
% 31.38/4.50  --prolific_symb_bound                   200
% 31.38/4.50  --lt_threshold                          2000
% 31.38/4.50  --clause_weak_htbl                      true
% 31.38/4.50  --gc_record_bc_elim                     false
% 31.38/4.50  
% 31.38/4.50  ------ Preprocessing Options
% 31.38/4.50  
% 31.38/4.50  --preprocessing_flag                    true
% 31.38/4.50  --time_out_prep_mult                    0.1
% 31.38/4.50  --splitting_mode                        input
% 31.38/4.50  --splitting_grd                         true
% 31.38/4.50  --splitting_cvd                         false
% 31.38/4.50  --splitting_cvd_svl                     false
% 31.38/4.50  --splitting_nvd                         32
% 31.38/4.50  --sub_typing                            true
% 31.38/4.50  --prep_gs_sim                           true
% 31.38/4.50  --prep_unflatten                        true
% 31.38/4.50  --prep_res_sim                          true
% 31.38/4.50  --prep_upred                            true
% 31.38/4.50  --prep_sem_filter                       exhaustive
% 31.38/4.50  --prep_sem_filter_out                   false
% 31.38/4.50  --pred_elim                             true
% 31.38/4.50  --res_sim_input                         true
% 31.38/4.50  --eq_ax_congr_red                       true
% 31.38/4.50  --pure_diseq_elim                       true
% 31.38/4.50  --brand_transform                       false
% 31.38/4.50  --non_eq_to_eq                          false
% 31.38/4.50  --prep_def_merge                        true
% 31.38/4.50  --prep_def_merge_prop_impl              false
% 31.38/4.50  --prep_def_merge_mbd                    true
% 31.38/4.50  --prep_def_merge_tr_red                 false
% 31.38/4.50  --prep_def_merge_tr_cl                  false
% 31.38/4.50  --smt_preprocessing                     true
% 31.38/4.50  --smt_ac_axioms                         fast
% 31.38/4.50  --preprocessed_out                      false
% 31.38/4.50  --preprocessed_stats                    false
% 31.38/4.50  
% 31.38/4.50  ------ Abstraction refinement Options
% 31.38/4.50  
% 31.38/4.50  --abstr_ref                             []
% 31.38/4.50  --abstr_ref_prep                        false
% 31.38/4.50  --abstr_ref_until_sat                   false
% 31.38/4.50  --abstr_ref_sig_restrict                funpre
% 31.38/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.38/4.50  --abstr_ref_under                       []
% 31.38/4.50  
% 31.38/4.50  ------ SAT Options
% 31.38/4.50  
% 31.38/4.50  --sat_mode                              false
% 31.38/4.50  --sat_fm_restart_options                ""
% 31.38/4.50  --sat_gr_def                            false
% 31.38/4.50  --sat_epr_types                         true
% 31.38/4.50  --sat_non_cyclic_types                  false
% 31.38/4.50  --sat_finite_models                     false
% 31.38/4.50  --sat_fm_lemmas                         false
% 31.38/4.50  --sat_fm_prep                           false
% 31.38/4.50  --sat_fm_uc_incr                        true
% 31.38/4.50  --sat_out_model                         small
% 31.38/4.50  --sat_out_clauses                       false
% 31.38/4.50  
% 31.38/4.50  ------ QBF Options
% 31.38/4.50  
% 31.38/4.50  --qbf_mode                              false
% 31.38/4.50  --qbf_elim_univ                         false
% 31.38/4.50  --qbf_dom_inst                          none
% 31.38/4.50  --qbf_dom_pre_inst                      false
% 31.38/4.50  --qbf_sk_in                             false
% 31.38/4.50  --qbf_pred_elim                         true
% 31.38/4.50  --qbf_split                             512
% 31.38/4.50  
% 31.38/4.50  ------ BMC1 Options
% 31.38/4.50  
% 31.38/4.50  --bmc1_incremental                      false
% 31.38/4.50  --bmc1_axioms                           reachable_all
% 31.38/4.50  --bmc1_min_bound                        0
% 31.38/4.50  --bmc1_max_bound                        -1
% 31.38/4.50  --bmc1_max_bound_default                -1
% 31.38/4.50  --bmc1_symbol_reachability              true
% 31.38/4.50  --bmc1_property_lemmas                  false
% 31.38/4.50  --bmc1_k_induction                      false
% 31.38/4.50  --bmc1_non_equiv_states                 false
% 31.38/4.50  --bmc1_deadlock                         false
% 31.38/4.50  --bmc1_ucm                              false
% 31.38/4.50  --bmc1_add_unsat_core                   none
% 31.38/4.50  --bmc1_unsat_core_children              false
% 31.38/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.38/4.50  --bmc1_out_stat                         full
% 31.38/4.50  --bmc1_ground_init                      false
% 31.38/4.50  --bmc1_pre_inst_next_state              false
% 31.38/4.50  --bmc1_pre_inst_state                   false
% 31.38/4.50  --bmc1_pre_inst_reach_state             false
% 31.38/4.50  --bmc1_out_unsat_core                   false
% 31.38/4.50  --bmc1_aig_witness_out                  false
% 31.38/4.50  --bmc1_verbose                          false
% 31.38/4.50  --bmc1_dump_clauses_tptp                false
% 31.38/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.38/4.50  --bmc1_dump_file                        -
% 31.38/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.38/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.38/4.50  --bmc1_ucm_extend_mode                  1
% 31.38/4.50  --bmc1_ucm_init_mode                    2
% 31.38/4.50  --bmc1_ucm_cone_mode                    none
% 31.38/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.38/4.50  --bmc1_ucm_relax_model                  4
% 31.38/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.38/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.38/4.50  --bmc1_ucm_layered_model                none
% 31.38/4.50  --bmc1_ucm_max_lemma_size               10
% 31.38/4.50  
% 31.38/4.50  ------ AIG Options
% 31.38/4.50  
% 31.38/4.50  --aig_mode                              false
% 31.38/4.50  
% 31.38/4.50  ------ Instantiation Options
% 31.38/4.50  
% 31.38/4.50  --instantiation_flag                    true
% 31.38/4.50  --inst_sos_flag                         true
% 31.38/4.50  --inst_sos_phase                        true
% 31.38/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.38/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.38/4.50  --inst_lit_sel_side                     none
% 31.38/4.50  --inst_solver_per_active                1400
% 31.38/4.50  --inst_solver_calls_frac                1.
% 31.38/4.50  --inst_passive_queue_type               priority_queues
% 31.38/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.38/4.50  --inst_passive_queues_freq              [25;2]
% 31.38/4.50  --inst_dismatching                      true
% 31.38/4.50  --inst_eager_unprocessed_to_passive     true
% 31.38/4.50  --inst_prop_sim_given                   true
% 31.38/4.50  --inst_prop_sim_new                     false
% 31.38/4.50  --inst_subs_new                         false
% 31.38/4.50  --inst_eq_res_simp                      false
% 31.38/4.50  --inst_subs_given                       false
% 31.38/4.50  --inst_orphan_elimination               true
% 31.38/4.50  --inst_learning_loop_flag               true
% 31.38/4.50  --inst_learning_start                   3000
% 31.38/4.50  --inst_learning_factor                  2
% 31.38/4.50  --inst_start_prop_sim_after_learn       3
% 31.38/4.50  --inst_sel_renew                        solver
% 31.38/4.50  --inst_lit_activity_flag                true
% 31.38/4.50  --inst_restr_to_given                   false
% 31.38/4.50  --inst_activity_threshold               500
% 31.38/4.50  --inst_out_proof                        true
% 31.38/4.50  
% 31.38/4.50  ------ Resolution Options
% 31.38/4.50  
% 31.38/4.50  --resolution_flag                       false
% 31.38/4.50  --res_lit_sel                           adaptive
% 31.38/4.50  --res_lit_sel_side                      none
% 31.38/4.50  --res_ordering                          kbo
% 31.38/4.50  --res_to_prop_solver                    active
% 31.38/4.50  --res_prop_simpl_new                    false
% 31.38/4.50  --res_prop_simpl_given                  true
% 31.38/4.50  --res_passive_queue_type                priority_queues
% 31.38/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.38/4.50  --res_passive_queues_freq               [15;5]
% 31.38/4.50  --res_forward_subs                      full
% 31.38/4.50  --res_backward_subs                     full
% 31.38/4.50  --res_forward_subs_resolution           true
% 31.38/4.50  --res_backward_subs_resolution          true
% 31.38/4.50  --res_orphan_elimination                true
% 31.38/4.50  --res_time_limit                        2.
% 31.38/4.50  --res_out_proof                         true
% 31.38/4.50  
% 31.38/4.50  ------ Superposition Options
% 31.38/4.50  
% 31.38/4.50  --superposition_flag                    true
% 31.38/4.50  --sup_passive_queue_type                priority_queues
% 31.38/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.38/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.38/4.50  --demod_completeness_check              fast
% 31.38/4.50  --demod_use_ground                      true
% 31.38/4.50  --sup_to_prop_solver                    passive
% 31.38/4.50  --sup_prop_simpl_new                    true
% 31.38/4.50  --sup_prop_simpl_given                  true
% 31.38/4.50  --sup_fun_splitting                     true
% 31.38/4.50  --sup_smt_interval                      50000
% 31.38/4.50  
% 31.38/4.50  ------ Superposition Simplification Setup
% 31.38/4.50  
% 31.38/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.38/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.38/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.38/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.38/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.38/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.38/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.38/4.50  --sup_immed_triv                        [TrivRules]
% 31.38/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.38/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.38/4.50  --sup_immed_bw_main                     []
% 31.38/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.38/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.38/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.38/4.50  --sup_input_bw                          []
% 31.38/4.50  
% 31.38/4.50  ------ Combination Options
% 31.38/4.50  
% 31.38/4.50  --comb_res_mult                         3
% 31.38/4.50  --comb_sup_mult                         2
% 31.38/4.50  --comb_inst_mult                        10
% 31.38/4.50  
% 31.38/4.50  ------ Debug Options
% 31.38/4.50  
% 31.38/4.50  --dbg_backtrace                         false
% 31.38/4.50  --dbg_dump_prop_clauses                 false
% 31.38/4.50  --dbg_dump_prop_clauses_file            -
% 31.38/4.50  --dbg_out_stat                          false
% 31.38/4.50  
% 31.38/4.50  
% 31.38/4.50  
% 31.38/4.50  
% 31.38/4.50  ------ Proving...
% 31.38/4.50  
% 31.38/4.50  
% 31.38/4.50  % SZS status Theorem for theBenchmark.p
% 31.38/4.50  
% 31.38/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.38/4.50  
% 31.38/4.50  fof(f6,axiom,(
% 31.38/4.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f15,plain,(
% 31.38/4.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 31.38/4.50    inference(ennf_transformation,[],[f6])).
% 31.38/4.50  
% 31.38/4.50  fof(f16,plain,(
% 31.38/4.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 31.38/4.50    inference(flattening,[],[f15])).
% 31.38/4.50  
% 31.38/4.50  fof(f37,plain,(
% 31.38/4.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 31.38/4.50    inference(cnf_transformation,[],[f16])).
% 31.38/4.50  
% 31.38/4.50  fof(f5,axiom,(
% 31.38/4.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f36,plain,(
% 31.38/4.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.38/4.50    inference(cnf_transformation,[],[f5])).
% 31.38/4.50  
% 31.38/4.50  fof(f2,axiom,(
% 31.38/4.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f13,plain,(
% 31.38/4.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 31.38/4.50    inference(ennf_transformation,[],[f2])).
% 31.38/4.50  
% 31.38/4.50  fof(f33,plain,(
% 31.38/4.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 31.38/4.50    inference(cnf_transformation,[],[f13])).
% 31.38/4.50  
% 31.38/4.50  fof(f11,conjecture,(
% 31.38/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f12,negated_conjecture,(
% 31.38/4.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 31.38/4.50    inference(negated_conjecture,[],[f11])).
% 31.38/4.50  
% 31.38/4.50  fof(f22,plain,(
% 31.38/4.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 31.38/4.50    inference(ennf_transformation,[],[f12])).
% 31.38/4.50  
% 31.38/4.50  fof(f28,plain,(
% 31.38/4.50    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.38/4.50    introduced(choice_axiom,[])).
% 31.38/4.50  
% 31.38/4.50  fof(f27,plain,(
% 31.38/4.50    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.38/4.50    introduced(choice_axiom,[])).
% 31.38/4.50  
% 31.38/4.50  fof(f26,plain,(
% 31.38/4.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 31.38/4.50    introduced(choice_axiom,[])).
% 31.38/4.50  
% 31.38/4.50  fof(f29,plain,(
% 31.38/4.50    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 31.38/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28,f27,f26])).
% 31.38/4.50  
% 31.38/4.50  fof(f44,plain,(
% 31.38/4.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.38/4.50    inference(cnf_transformation,[],[f29])).
% 31.38/4.50  
% 31.38/4.50  fof(f8,axiom,(
% 31.38/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f25,plain,(
% 31.38/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.38/4.50    inference(nnf_transformation,[],[f8])).
% 31.38/4.50  
% 31.38/4.50  fof(f39,plain,(
% 31.38/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.38/4.50    inference(cnf_transformation,[],[f25])).
% 31.38/4.50  
% 31.38/4.50  fof(f1,axiom,(
% 31.38/4.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f23,plain,(
% 31.38/4.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.38/4.50    inference(nnf_transformation,[],[f1])).
% 31.38/4.50  
% 31.38/4.50  fof(f24,plain,(
% 31.38/4.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.38/4.50    inference(flattening,[],[f23])).
% 31.38/4.50  
% 31.38/4.50  fof(f32,plain,(
% 31.38/4.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.38/4.50    inference(cnf_transformation,[],[f24])).
% 31.38/4.50  
% 31.38/4.50  fof(f30,plain,(
% 31.38/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.38/4.50    inference(cnf_transformation,[],[f24])).
% 31.38/4.50  
% 31.38/4.50  fof(f48,plain,(
% 31.38/4.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.38/4.50    inference(equality_resolution,[],[f30])).
% 31.38/4.50  
% 31.38/4.50  fof(f3,axiom,(
% 31.38/4.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f34,plain,(
% 31.38/4.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 31.38/4.50    inference(cnf_transformation,[],[f3])).
% 31.38/4.50  
% 31.38/4.50  fof(f9,axiom,(
% 31.38/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f19,plain,(
% 31.38/4.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.38/4.50    inference(ennf_transformation,[],[f9])).
% 31.38/4.50  
% 31.38/4.50  fof(f41,plain,(
% 31.38/4.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.38/4.50    inference(cnf_transformation,[],[f19])).
% 31.38/4.50  
% 31.38/4.50  fof(f43,plain,(
% 31.38/4.50    l1_pre_topc(sK0)),
% 31.38/4.50    inference(cnf_transformation,[],[f29])).
% 31.38/4.50  
% 31.38/4.50  fof(f4,axiom,(
% 31.38/4.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f14,plain,(
% 31.38/4.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 31.38/4.50    inference(ennf_transformation,[],[f4])).
% 31.38/4.50  
% 31.38/4.50  fof(f35,plain,(
% 31.38/4.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 31.38/4.50    inference(cnf_transformation,[],[f14])).
% 31.38/4.50  
% 31.38/4.50  fof(f45,plain,(
% 31.38/4.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.38/4.50    inference(cnf_transformation,[],[f29])).
% 31.38/4.50  
% 31.38/4.50  fof(f10,axiom,(
% 31.38/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f20,plain,(
% 31.38/4.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.38/4.50    inference(ennf_transformation,[],[f10])).
% 31.38/4.50  
% 31.38/4.50  fof(f21,plain,(
% 31.38/4.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.38/4.50    inference(flattening,[],[f20])).
% 31.38/4.50  
% 31.38/4.50  fof(f42,plain,(
% 31.38/4.50    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.38/4.50    inference(cnf_transformation,[],[f21])).
% 31.38/4.50  
% 31.38/4.50  fof(f40,plain,(
% 31.38/4.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.38/4.50    inference(cnf_transformation,[],[f25])).
% 31.38/4.50  
% 31.38/4.50  fof(f7,axiom,(
% 31.38/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 31.38/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.38/4.50  
% 31.38/4.50  fof(f17,plain,(
% 31.38/4.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.38/4.50    inference(ennf_transformation,[],[f7])).
% 31.38/4.50  
% 31.38/4.50  fof(f18,plain,(
% 31.38/4.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.38/4.50    inference(flattening,[],[f17])).
% 31.38/4.50  
% 31.38/4.50  fof(f38,plain,(
% 31.38/4.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.38/4.50    inference(cnf_transformation,[],[f18])).
% 31.38/4.50  
% 31.38/4.50  fof(f31,plain,(
% 31.38/4.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 31.38/4.50    inference(cnf_transformation,[],[f24])).
% 31.38/4.50  
% 31.38/4.50  fof(f47,plain,(
% 31.38/4.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.38/4.50    inference(equality_resolution,[],[f31])).
% 31.38/4.50  
% 31.38/4.50  fof(f46,plain,(
% 31.38/4.50    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 31.38/4.50    inference(cnf_transformation,[],[f29])).
% 31.38/4.50  
% 31.38/4.50  cnf(c_7,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1)
% 31.38/4.50      | ~ r1_tarski(X2,X1)
% 31.38/4.50      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 31.38/4.50      inference(cnf_transformation,[],[f37]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_76170,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_7]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_110084,plain,
% 31.38/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_76170]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_392,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.38/4.50      theory(equality) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_75888,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1)
% 31.38/4.50      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_392]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_75902,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_75888]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_75929,plain,
% 31.38/4.50      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0,X1)
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_75902]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_109581,plain,
% 31.38/4.50      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_75929]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_75932,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1)
% 31.38/4.50      | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | X2 != X0
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_392]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_76501,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
% 31.38/4.50      | r1_tarski(X3,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | X3 != X0
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_75932]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_78472,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,k1_tops_1(X1,k2_xboole_0(sK1,sK2)))
% 31.38/4.50      | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | X2 != X0
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,k2_xboole_0(sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_76501]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_82353,plain,
% 31.38/4.50      ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.38/4.50      | X0 != k1_tops_1(sK0,X1)
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_78472]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_88076,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.38/4.50      | k1_tops_1(sK0,X0) != k1_tops_1(sK0,X0)
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_82353]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_104141,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.38/4.50      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_88076]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_77430,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1)
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X2,X3))
% 31.38/4.50      | k1_tops_1(X2,X3) != X1
% 31.38/4.50      | k1_tops_1(sK0,sK2) != X0 ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_392]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_80370,plain,
% 31.38/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X1,X2))
% 31.38/4.50      | k1_tops_1(X1,X2) != X0
% 31.38/4.50      | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_77430]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_87932,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X0,X1))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.38/4.50      | k1_tops_1(X0,X1) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.38/4.50      | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_80370]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_104127,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.38/4.50      | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_87932]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_6,plain,
% 31.38/4.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 31.38/4.50      inference(cnf_transformation,[],[f36]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15073,plain,
% 31.38/4.50      ( r1_tarski(sK1,k2_xboole_0(sK1,X0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_6]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_75065,plain,
% 31.38/4.50      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_15073]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_3,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 31.38/4.50      inference(cnf_transformation,[],[f33]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_16602,plain,
% 31.38/4.50      ( r1_tarski(X0,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(X0,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_50791,plain,
% 31.38/4.50      ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(sK2,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_16602]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15,negated_conjecture,
% 31.38/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.38/4.50      inference(cnf_transformation,[],[f44]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_730,plain,
% 31.38/4.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_10,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.38/4.50      inference(cnf_transformation,[],[f39]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_733,plain,
% 31.38/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.38/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1422,plain,
% 31.38/4.50      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_730,c_733]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_735,plain,
% 31.38/4.50      ( r1_tarski(X0,X1) != iProver_top
% 31.38/4.50      | r1_tarski(X2,X1) != iProver_top
% 31.38/4.50      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_736,plain,
% 31.38/4.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_0,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.38/4.50      inference(cnf_transformation,[],[f32]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_741,plain,
% 31.38/4.50      ( X0 = X1
% 31.38/4.50      | r1_tarski(X0,X1) != iProver_top
% 31.38/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_2228,plain,
% 31.38/4.50      ( k2_xboole_0(X0,X1) = X0
% 31.38/4.50      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_736,c_741]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_8146,plain,
% 31.38/4.50      ( k2_xboole_0(X0,X1) = X0
% 31.38/4.50      | r1_tarski(X0,X0) != iProver_top
% 31.38/4.50      | r1_tarski(X1,X0) != iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_735,c_2228]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_2,plain,
% 31.38/4.50      ( r1_tarski(X0,X0) ),
% 31.38/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_47,plain,
% 31.38/4.50      ( r1_tarski(X0,X0) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15914,plain,
% 31.38/4.50      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 31.38/4.50      inference(global_propositional_subsumption,
% 31.38/4.50                [status(thm)],
% 31.38/4.50                [c_8146,c_47]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15924,plain,
% 31.38/4.50      ( k2_xboole_0(u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_1422,c_15914]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_4,plain,
% 31.38/4.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 31.38/4.50      inference(cnf_transformation,[],[f34]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_738,plain,
% 31.38/4.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_11,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.38/4.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 31.38/4.50      | ~ l1_pre_topc(X1) ),
% 31.38/4.50      inference(cnf_transformation,[],[f41]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_16,negated_conjecture,
% 31.38/4.50      ( l1_pre_topc(sK0) ),
% 31.38/4.50      inference(cnf_transformation,[],[f43]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_234,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.38/4.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 31.38/4.50      | sK0 != X1 ),
% 31.38/4.50      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_235,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 31.38/4.50      inference(unflattening,[status(thm)],[c_234]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_728,plain,
% 31.38/4.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_969,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_730,c_728]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15928,plain,
% 31.38/4.50      ( k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_969,c_15914]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_739,plain,
% 31.38/4.50      ( r1_tarski(X0,X1) != iProver_top
% 31.38/4.50      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_17409,plain,
% 31.38/4.50      ( r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 31.38/4.50      | r1_tarski(X0,sK1) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_15928,c_739]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_18661,plain,
% 31.38/4.50      ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),X0),sK1) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_738,c_17409]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_5,plain,
% 31.38/4.50      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 31.38/4.50      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 31.38/4.50      inference(cnf_transformation,[],[f35]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_737,plain,
% 31.38/4.50      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 31.38/4.50      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_19002,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1)) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_18661,c_737]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_19032,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_15924,c_19002]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_14,negated_conjecture,
% 31.38/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.38/4.50      inference(cnf_transformation,[],[f45]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_731,plain,
% 31.38/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1421,plain,
% 31.38/4.50      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_731,c_733]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15923,plain,
% 31.38/4.50      ( k2_xboole_0(u1_struct_0(sK0),sK2) = u1_struct_0(sK0) ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_1421,c_15914]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_968,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_731,c_728]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15927,plain,
% 31.38/4.50      ( k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) = sK2 ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_968,c_15914]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_17023,plain,
% 31.38/4.50      ( r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
% 31.38/4.50      | r1_tarski(X0,sK2) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_15927,c_739]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_18482,plain,
% 31.38/4.50      ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK2),X0),sK2) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_738,c_17023]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_18537,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(X0,sK2)) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_18482,c_737]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_18567,plain,
% 31.38/4.50      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_15923,c_18537]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_12,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.38/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.38/4.50      | ~ r1_tarski(X0,X2)
% 31.38/4.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 31.38/4.50      | ~ l1_pre_topc(X1) ),
% 31.38/4.50      inference(cnf_transformation,[],[f42]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_216,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.38/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.38/4.50      | ~ r1_tarski(X0,X2)
% 31.38/4.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 31.38/4.50      | sK0 != X1 ),
% 31.38/4.50      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_217,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ r1_tarski(X1,X0)
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 31.38/4.50      inference(unflattening,[status(thm)],[c_216]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_8036,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_217]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15214,plain,
% 31.38/4.50      ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_8036]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_15211,plain,
% 31.38/4.50      ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.38/4.50      | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_8036]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_4309,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 31.38/4.50      | X0 = k1_tops_1(sK0,sK1) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_0]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_10995,plain,
% 31.38/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
% 31.38/4.50      | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_4309]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_2537,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK2))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
% 31.38/4.50      | X0 = k1_tops_1(sK0,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_0]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_6339,plain,
% 31.38/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
% 31.38/4.50      | k1_tops_1(sK0,sK2) = k1_tops_1(sK0,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_2537]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_9,plain,
% 31.38/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.38/4.50      inference(cnf_transformation,[],[f40]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_776,plain,
% 31.38/4.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_9]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_925,plain,
% 31.38/4.50      ( m1_subset_1(k2_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_776]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_4295,plain,
% 31.38/4.50      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_925]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_396,plain,
% 31.38/4.50      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 31.38/4.50      theory(equality) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1732,plain,
% 31.38/4.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 31.38/4.50      | sK0 != X1 ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_396]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_3572,plain,
% 31.38/4.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
% 31.38/4.50      | sK0 != X0 ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_1732]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_3573,plain,
% 31.38/4.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.38/4.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.38/4.50      | sK0 != sK0 ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_3572]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1325,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 31.38/4.50      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 31.38/4.50      | r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_7]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_2107,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 31.38/4.50      | r1_tarski(k2_xboole_0(sK1,X0),u1_struct_0(sK0))
% 31.38/4.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_1325]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_2576,plain,
% 31.38/4.50      ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 31.38/4.50      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.38/4.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_2107]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_8,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.38/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.38/4.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.38/4.50      inference(cnf_transformation,[],[f38]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_127,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.38/4.50      inference(prop_impl,[status(thm)],[c_9]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_128,plain,
% 31.38/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.38/4.50      inference(renaming,[status(thm)],[c_127]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_155,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.38/4.50      | ~ r1_tarski(X2,X1)
% 31.38/4.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.38/4.50      inference(bin_hyper_res,[status(thm)],[c_8,c_128]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_306,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.38/4.50      inference(prop_impl,[status(thm)],[c_9]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_307,plain,
% 31.38/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.38/4.50      inference(renaming,[status(thm)],[c_306]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_332,plain,
% 31.38/4.50      ( ~ r1_tarski(X0,X1)
% 31.38/4.50      | ~ r1_tarski(X2,X1)
% 31.38/4.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.38/4.50      inference(bin_hyper_res,[status(thm)],[c_155,c_307]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_727,plain,
% 31.38/4.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 31.38/4.50      | r1_tarski(X1,X0) != iProver_top
% 31.38/4.50      | r1_tarski(X2,X0) != iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1652,plain,
% 31.38/4.50      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 31.38/4.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_1422,c_727]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1826,plain,
% 31.38/4.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 31.38/4.50      inference(superposition,[status(thm)],[c_1421,c_1652]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1625,plain,
% 31.38/4.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 31.38/4.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 31.38/4.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_332]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1626,plain,
% 31.38/4.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
% 31.38/4.50      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_912,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_10]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1153,plain,
% 31.38/4.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_912]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1150,plain,
% 31.38/4.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_912]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_390,plain,( X0 = X0 ),theory(equality) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_956,plain,
% 31.38/4.50      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_390]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_1,plain,
% 31.38/4.50      ( r1_tarski(X0,X0) ),
% 31.38/4.50      inference(cnf_transformation,[],[f47]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_908,plain,
% 31.38/4.50      ( r1_tarski(sK1,sK1) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_1]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_901,plain,
% 31.38/4.50      ( r1_tarski(sK2,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_1]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_791,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ r1_tarski(X0,sK1)
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_217]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_846,plain,
% 31.38/4.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
% 31.38/4.50      | ~ r1_tarski(sK1,sK1) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_791]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_786,plain,
% 31.38/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | ~ r1_tarski(X0,sK2)
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_217]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_820,plain,
% 31.38/4.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.38/4.50      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
% 31.38/4.50      | ~ r1_tarski(sK2,sK2) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_786]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_52,plain,
% 31.38/4.50      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_0]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_48,plain,
% 31.38/4.50      ( r1_tarski(sK0,sK0) ),
% 31.38/4.50      inference(instantiation,[status(thm)],[c_2]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(c_13,negated_conjecture,
% 31.38/4.50      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.38/4.50      inference(cnf_transformation,[],[f46]) ).
% 31.38/4.50  
% 31.38/4.50  cnf(contradiction,plain,
% 31.38/4.50      ( $false ),
% 31.38/4.50      inference(minisat,
% 31.38/4.50                [status(thm)],
% 31.38/4.50                [c_110084,c_109581,c_104141,c_104127,c_75065,c_50791,
% 31.38/4.50                 c_19032,c_18567,c_15214,c_15211,c_10995,c_6339,c_4295,
% 31.38/4.50                 c_3573,c_2576,c_1826,c_1626,c_1153,c_1150,c_956,c_908,
% 31.38/4.50                 c_901,c_846,c_820,c_52,c_48,c_13,c_14,c_15]) ).
% 31.38/4.50  
% 31.38/4.50  
% 31.38/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.38/4.50  
% 31.38/4.50  ------                               Statistics
% 31.38/4.50  
% 31.38/4.50  ------ General
% 31.38/4.50  
% 31.38/4.50  abstr_ref_over_cycles:                  0
% 31.38/4.50  abstr_ref_under_cycles:                 0
% 31.38/4.50  gc_basic_clause_elim:                   0
% 31.38/4.50  forced_gc_time:                         0
% 31.38/4.50  parsing_time:                           0.008
% 31.38/4.50  unif_index_cands_time:                  0.
% 31.38/4.50  unif_index_add_time:                    0.
% 31.38/4.50  orderings_time:                         0.
% 31.38/4.50  out_proof_time:                         0.021
% 31.38/4.50  total_time:                             3.61
% 31.38/4.50  num_of_symbols:                         43
% 31.38/4.50  num_of_terms:                           147424
% 31.38/4.50  
% 31.38/4.50  ------ Preprocessing
% 31.38/4.50  
% 31.38/4.50  num_of_splits:                          0
% 31.38/4.50  num_of_split_atoms:                     0
% 31.38/4.50  num_of_reused_defs:                     0
% 31.38/4.50  num_eq_ax_congr_red:                    12
% 31.38/4.50  num_of_sem_filtered_clauses:            1
% 31.38/4.50  num_of_subtypes:                        0
% 31.38/4.50  monotx_restored_types:                  0
% 31.38/4.50  sat_num_of_epr_types:                   0
% 31.38/4.50  sat_num_of_non_cyclic_types:            0
% 31.38/4.50  sat_guarded_non_collapsed_types:        0
% 31.38/4.50  num_pure_diseq_elim:                    0
% 31.38/4.50  simp_replaced_by:                       0
% 31.38/4.50  res_preprocessed:                       78
% 31.38/4.50  prep_upred:                             0
% 31.38/4.50  prep_unflattend:                        2
% 31.38/4.50  smt_new_axioms:                         0
% 31.38/4.50  pred_elim_cands:                        2
% 31.38/4.50  pred_elim:                              1
% 31.38/4.50  pred_elim_cl:                           1
% 31.38/4.50  pred_elim_cycles:                       3
% 31.38/4.50  merged_defs:                            8
% 31.38/4.50  merged_defs_ncl:                        0
% 31.38/4.50  bin_hyper_res:                          10
% 31.38/4.50  prep_cycles:                            4
% 31.38/4.50  pred_elim_time:                         0.001
% 31.38/4.50  splitting_time:                         0.
% 31.38/4.50  sem_filter_time:                        0.
% 31.38/4.50  monotx_time:                            0.001
% 31.38/4.50  subtype_inf_time:                       0.
% 31.38/4.50  
% 31.38/4.50  ------ Problem properties
% 31.38/4.50  
% 31.38/4.50  clauses:                                15
% 31.38/4.50  conjectures:                            3
% 31.38/4.50  epr:                                    2
% 31.38/4.50  horn:                                   15
% 31.38/4.50  ground:                                 3
% 31.38/4.50  unary:                                  6
% 31.38/4.50  binary:                                 5
% 31.38/4.50  lits:                                   29
% 31.38/4.50  lits_eq:                                2
% 31.38/4.50  fd_pure:                                0
% 31.38/4.50  fd_pseudo:                              0
% 31.38/4.50  fd_cond:                                0
% 31.38/4.50  fd_pseudo_cond:                         1
% 31.38/4.50  ac_symbols:                             0
% 31.38/4.50  
% 31.38/4.50  ------ Propositional Solver
% 31.38/4.50  
% 31.38/4.50  prop_solver_calls:                      52
% 31.38/4.50  prop_fast_solver_calls:                 2282
% 31.38/4.50  smt_solver_calls:                       0
% 31.38/4.50  smt_fast_solver_calls:                  0
% 31.38/4.50  prop_num_of_clauses:                    51534
% 31.38/4.50  prop_preprocess_simplified:             60460
% 31.38/4.50  prop_fo_subsumed:                       71
% 31.38/4.50  prop_solver_time:                       0.
% 31.38/4.50  smt_solver_time:                        0.
% 31.38/4.50  smt_fast_solver_time:                   0.
% 31.38/4.50  prop_fast_solver_time:                  0.
% 31.38/4.50  prop_unsat_core_time:                   0.007
% 31.38/4.50  
% 31.38/4.50  ------ QBF
% 31.38/4.50  
% 31.38/4.50  qbf_q_res:                              0
% 31.38/4.50  qbf_num_tautologies:                    0
% 31.38/4.50  qbf_prep_cycles:                        0
% 31.38/4.50  
% 31.38/4.50  ------ BMC1
% 31.38/4.50  
% 31.38/4.50  bmc1_current_bound:                     -1
% 31.38/4.50  bmc1_last_solved_bound:                 -1
% 31.38/4.50  bmc1_unsat_core_size:                   -1
% 31.38/4.50  bmc1_unsat_core_parents_size:           -1
% 31.38/4.50  bmc1_merge_next_fun:                    0
% 31.38/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.38/4.50  
% 31.38/4.50  ------ Instantiation
% 31.38/4.50  
% 31.38/4.50  inst_num_of_clauses:                    2673
% 31.38/4.50  inst_num_in_passive:                    824
% 31.38/4.50  inst_num_in_active:                     3786
% 31.38/4.50  inst_num_in_unprocessed:                772
% 31.38/4.50  inst_num_of_loops:                      4150
% 31.38/4.50  inst_num_of_learning_restarts:          1
% 31.38/4.50  inst_num_moves_active_passive:          362
% 31.38/4.50  inst_lit_activity:                      0
% 31.38/4.50  inst_lit_activity_moves:                6
% 31.38/4.50  inst_num_tautologies:                   0
% 31.38/4.50  inst_num_prop_implied:                  0
% 31.38/4.50  inst_num_existing_simplified:           0
% 31.38/4.50  inst_num_eq_res_simplified:             0
% 31.38/4.50  inst_num_child_elim:                    0
% 31.38/4.50  inst_num_of_dismatching_blockings:      18089
% 31.38/4.50  inst_num_of_non_proper_insts:           14755
% 31.38/4.50  inst_num_of_duplicates:                 0
% 31.38/4.50  inst_inst_num_from_inst_to_res:         0
% 31.38/4.50  inst_dismatching_checking_time:         0.
% 31.38/4.50  
% 31.38/4.50  ------ Resolution
% 31.38/4.50  
% 31.38/4.50  res_num_of_clauses:                     23
% 31.38/4.50  res_num_in_passive:                     23
% 31.38/4.50  res_num_in_active:                      0
% 31.38/4.50  res_num_of_loops:                       82
% 31.38/4.50  res_forward_subset_subsumed:            432
% 31.38/4.50  res_backward_subset_subsumed:           6
% 31.38/4.50  res_forward_subsumed:                   0
% 31.38/4.50  res_backward_subsumed:                  0
% 31.38/4.50  res_forward_subsumption_resolution:     0
% 31.38/4.50  res_backward_subsumption_resolution:    0
% 31.38/4.50  res_clause_to_clause_subsumption:       84666
% 31.38/4.50  res_orphan_elimination:                 0
% 31.38/4.50  res_tautology_del:                      380
% 31.38/4.50  res_num_eq_res_simplified:              0
% 31.38/4.50  res_num_sel_changes:                    0
% 31.38/4.50  res_moves_from_active_to_pass:          0
% 31.38/4.50  
% 31.38/4.50  ------ Superposition
% 31.38/4.50  
% 31.38/4.50  sup_time_total:                         0.
% 31.38/4.50  sup_time_generating:                    0.
% 31.38/4.50  sup_time_sim_full:                      0.
% 31.38/4.50  sup_time_sim_immed:                     0.
% 31.38/4.50  
% 31.38/4.50  sup_num_of_clauses:                     6668
% 31.38/4.50  sup_num_in_active:                      722
% 31.38/4.50  sup_num_in_passive:                     5946
% 31.38/4.50  sup_num_of_loops:                       830
% 31.38/4.50  sup_fw_superposition:                   8157
% 31.38/4.50  sup_bw_superposition:                   7120
% 31.38/4.50  sup_immediate_simplified:               7063
% 31.38/4.50  sup_given_eliminated:                   30
% 31.38/4.50  comparisons_done:                       0
% 31.38/4.50  comparisons_avoided:                    0
% 31.38/4.50  
% 31.38/4.50  ------ Simplifications
% 31.38/4.50  
% 31.38/4.50  
% 31.38/4.50  sim_fw_subset_subsumed:                 238
% 31.38/4.50  sim_bw_subset_subsumed:                 19
% 31.38/4.50  sim_fw_subsumed:                        1648
% 31.38/4.50  sim_bw_subsumed:                        150
% 31.38/4.50  sim_fw_subsumption_res:                 0
% 31.38/4.50  sim_bw_subsumption_res:                 0
% 31.38/4.50  sim_tautology_del:                      414
% 31.38/4.50  sim_eq_tautology_del:                   1331
% 31.38/4.50  sim_eq_res_simp:                        0
% 31.38/4.50  sim_fw_demodulated:                     4079
% 31.38/4.50  sim_bw_demodulated:                     125
% 31.38/4.50  sim_light_normalised:                   1564
% 31.38/4.50  sim_joinable_taut:                      0
% 31.38/4.50  sim_joinable_simp:                      0
% 31.38/4.50  sim_ac_normalised:                      0
% 31.38/4.50  sim_smt_subsumption:                    0
% 31.38/4.50  
%------------------------------------------------------------------------------
