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
% DateTime   : Thu Dec  3 12:13:50 EST 2020

% Result     : Theorem 35.73s
% Output     : CNFRefutation 35.73s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 215 expanded)
%              Number of clauses        :   71 (  86 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  326 ( 730 expanded)
%              Number of equality atoms :   90 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f28,f27,f26])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
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

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_152,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_153,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_82893,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_130530,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_82893])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_81414,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_119843,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_81414])).

cnf(c_277,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_75582,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_75915,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_75582])).

cnf(c_86342,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(X2,X3))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0,X1)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X2,X3) ),
    inference(instantiation,[status(thm)],[c_75915])).

cnf(c_88477,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(X2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0,X1)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_86342])).

cnf(c_113938,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_88477])).

cnf(c_113940,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_113938])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_76843,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != X2
    | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_79301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_76843])).

cnf(c_82500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_xboole_0(X1,X2) != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_79301])).

cnf(c_87900,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)) != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_82500])).

cnf(c_98588,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)) != k2_xboole_0(sK1,sK2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_87900])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_80240,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,X0),X1)
    | r1_tarski(sK2,k2_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_81413,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,X0))
    | r1_tarski(sK2,k2_xboole_0(X0,k4_xboole_0(sK2,X0))) ),
    inference(instantiation,[status(thm)],[c_80240])).

cnf(c_90822,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))
    | r1_tarski(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_81413])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_77111,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X0,X1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(X0,X1))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_79318,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_77111])).

cnf(c_86480,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))) ),
    inference(instantiation,[status(thm)],[c_79318])).

cnf(c_86479,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
    | ~ r1_tarski(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_82893])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_82357,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_282,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_837,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_56693,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_56694,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_56693])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_29815,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_276,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3786,plain,
    ( X0 != X1
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_8012,plain,
    ( X0 != k2_xboole_0(sK1,sK2)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = X0
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3786])).

cnf(c_29814,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_8012])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_493,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_494,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_496,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12071,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_496])).

cnf(c_16710,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_493,c_12071])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_497,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17413,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16710,c_497])).

cnf(c_17468,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17413])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5393,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_275,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4337,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_803,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_171,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_170])).

cnf(c_584,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_581,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_44,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_40,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130530,c_119843,c_113940,c_98588,c_90822,c_86480,c_86479,c_82357,c_56694,c_29815,c_29814,c_17468,c_5393,c_4337,c_803,c_584,c_581,c_44,c_40,c_11,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:08:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.73/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.73/4.99  
% 35.73/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.73/4.99  
% 35.73/4.99  ------  iProver source info
% 35.73/4.99  
% 35.73/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.73/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.73/4.99  git: non_committed_changes: false
% 35.73/4.99  git: last_make_outside_of_git: false
% 35.73/4.99  
% 35.73/4.99  ------ 
% 35.73/4.99  
% 35.73/4.99  ------ Input Options
% 35.73/4.99  
% 35.73/4.99  --out_options                           all
% 35.73/4.99  --tptp_safe_out                         true
% 35.73/4.99  --problem_path                          ""
% 35.73/4.99  --include_path                          ""
% 35.73/4.99  --clausifier                            res/vclausify_rel
% 35.73/4.99  --clausifier_options                    --mode clausify
% 35.73/4.99  --stdin                                 false
% 35.73/4.99  --stats_out                             all
% 35.73/4.99  
% 35.73/4.99  ------ General Options
% 35.73/4.99  
% 35.73/4.99  --fof                                   false
% 35.73/4.99  --time_out_real                         305.
% 35.73/4.99  --time_out_virtual                      -1.
% 35.73/4.99  --symbol_type_check                     false
% 35.73/4.99  --clausify_out                          false
% 35.73/4.99  --sig_cnt_out                           false
% 35.73/4.99  --trig_cnt_out                          false
% 35.73/4.99  --trig_cnt_out_tolerance                1.
% 35.73/4.99  --trig_cnt_out_sk_spl                   false
% 35.73/4.99  --abstr_cl_out                          false
% 35.73/4.99  
% 35.73/4.99  ------ Global Options
% 35.73/4.99  
% 35.73/4.99  --schedule                              default
% 35.73/4.99  --add_important_lit                     false
% 35.73/4.99  --prop_solver_per_cl                    1000
% 35.73/4.99  --min_unsat_core                        false
% 35.73/4.99  --soft_assumptions                      false
% 35.73/4.99  --soft_lemma_size                       3
% 35.73/4.99  --prop_impl_unit_size                   0
% 35.73/4.99  --prop_impl_unit                        []
% 35.73/4.99  --share_sel_clauses                     true
% 35.73/4.99  --reset_solvers                         false
% 35.73/4.99  --bc_imp_inh                            [conj_cone]
% 35.73/4.99  --conj_cone_tolerance                   3.
% 35.73/4.99  --extra_neg_conj                        none
% 35.73/4.99  --large_theory_mode                     true
% 35.73/4.99  --prolific_symb_bound                   200
% 35.73/4.99  --lt_threshold                          2000
% 35.73/4.99  --clause_weak_htbl                      true
% 35.73/4.99  --gc_record_bc_elim                     false
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing Options
% 35.73/4.99  
% 35.73/4.99  --preprocessing_flag                    true
% 35.73/4.99  --time_out_prep_mult                    0.1
% 35.73/4.99  --splitting_mode                        input
% 35.73/4.99  --splitting_grd                         true
% 35.73/4.99  --splitting_cvd                         false
% 35.73/4.99  --splitting_cvd_svl                     false
% 35.73/4.99  --splitting_nvd                         32
% 35.73/4.99  --sub_typing                            true
% 35.73/4.99  --prep_gs_sim                           true
% 35.73/4.99  --prep_unflatten                        true
% 35.73/4.99  --prep_res_sim                          true
% 35.73/4.99  --prep_upred                            true
% 35.73/4.99  --prep_sem_filter                       exhaustive
% 35.73/4.99  --prep_sem_filter_out                   false
% 35.73/4.99  --pred_elim                             true
% 35.73/4.99  --res_sim_input                         true
% 35.73/4.99  --eq_ax_congr_red                       true
% 35.73/4.99  --pure_diseq_elim                       true
% 35.73/4.99  --brand_transform                       false
% 35.73/4.99  --non_eq_to_eq                          false
% 35.73/4.99  --prep_def_merge                        true
% 35.73/4.99  --prep_def_merge_prop_impl              false
% 35.73/4.99  --prep_def_merge_mbd                    true
% 35.73/4.99  --prep_def_merge_tr_red                 false
% 35.73/4.99  --prep_def_merge_tr_cl                  false
% 35.73/4.99  --smt_preprocessing                     true
% 35.73/4.99  --smt_ac_axioms                         fast
% 35.73/4.99  --preprocessed_out                      false
% 35.73/4.99  --preprocessed_stats                    false
% 35.73/4.99  
% 35.73/4.99  ------ Abstraction refinement Options
% 35.73/4.99  
% 35.73/4.99  --abstr_ref                             []
% 35.73/4.99  --abstr_ref_prep                        false
% 35.73/4.99  --abstr_ref_until_sat                   false
% 35.73/4.99  --abstr_ref_sig_restrict                funpre
% 35.73/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.73/4.99  --abstr_ref_under                       []
% 35.73/4.99  
% 35.73/4.99  ------ SAT Options
% 35.73/4.99  
% 35.73/4.99  --sat_mode                              false
% 35.73/4.99  --sat_fm_restart_options                ""
% 35.73/4.99  --sat_gr_def                            false
% 35.73/4.99  --sat_epr_types                         true
% 35.73/4.99  --sat_non_cyclic_types                  false
% 35.73/4.99  --sat_finite_models                     false
% 35.73/4.99  --sat_fm_lemmas                         false
% 35.73/4.99  --sat_fm_prep                           false
% 35.73/4.99  --sat_fm_uc_incr                        true
% 35.73/4.99  --sat_out_model                         small
% 35.73/4.99  --sat_out_clauses                       false
% 35.73/4.99  
% 35.73/4.99  ------ QBF Options
% 35.73/4.99  
% 35.73/4.99  --qbf_mode                              false
% 35.73/4.99  --qbf_elim_univ                         false
% 35.73/4.99  --qbf_dom_inst                          none
% 35.73/4.99  --qbf_dom_pre_inst                      false
% 35.73/4.99  --qbf_sk_in                             false
% 35.73/4.99  --qbf_pred_elim                         true
% 35.73/4.99  --qbf_split                             512
% 35.73/4.99  
% 35.73/4.99  ------ BMC1 Options
% 35.73/4.99  
% 35.73/4.99  --bmc1_incremental                      false
% 35.73/4.99  --bmc1_axioms                           reachable_all
% 35.73/4.99  --bmc1_min_bound                        0
% 35.73/4.99  --bmc1_max_bound                        -1
% 35.73/4.99  --bmc1_max_bound_default                -1
% 35.73/4.99  --bmc1_symbol_reachability              true
% 35.73/4.99  --bmc1_property_lemmas                  false
% 35.73/4.99  --bmc1_k_induction                      false
% 35.73/4.99  --bmc1_non_equiv_states                 false
% 35.73/4.99  --bmc1_deadlock                         false
% 35.73/4.99  --bmc1_ucm                              false
% 35.73/4.99  --bmc1_add_unsat_core                   none
% 35.73/4.99  --bmc1_unsat_core_children              false
% 35.73/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.73/4.99  --bmc1_out_stat                         full
% 35.73/4.99  --bmc1_ground_init                      false
% 35.73/4.99  --bmc1_pre_inst_next_state              false
% 35.73/4.99  --bmc1_pre_inst_state                   false
% 35.73/4.99  --bmc1_pre_inst_reach_state             false
% 35.73/4.99  --bmc1_out_unsat_core                   false
% 35.73/4.99  --bmc1_aig_witness_out                  false
% 35.73/4.99  --bmc1_verbose                          false
% 35.73/4.99  --bmc1_dump_clauses_tptp                false
% 35.73/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.73/4.99  --bmc1_dump_file                        -
% 35.73/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.73/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.73/4.99  --bmc1_ucm_extend_mode                  1
% 35.73/4.99  --bmc1_ucm_init_mode                    2
% 35.73/4.99  --bmc1_ucm_cone_mode                    none
% 35.73/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.73/4.99  --bmc1_ucm_relax_model                  4
% 35.73/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.73/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.73/4.99  --bmc1_ucm_layered_model                none
% 35.73/4.99  --bmc1_ucm_max_lemma_size               10
% 35.73/4.99  
% 35.73/4.99  ------ AIG Options
% 35.73/4.99  
% 35.73/4.99  --aig_mode                              false
% 35.73/4.99  
% 35.73/4.99  ------ Instantiation Options
% 35.73/4.99  
% 35.73/4.99  --instantiation_flag                    true
% 35.73/4.99  --inst_sos_flag                         false
% 35.73/4.99  --inst_sos_phase                        true
% 35.73/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.73/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.73/4.99  --inst_lit_sel_side                     num_symb
% 35.73/4.99  --inst_solver_per_active                1400
% 35.73/4.99  --inst_solver_calls_frac                1.
% 35.73/4.99  --inst_passive_queue_type               priority_queues
% 35.73/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.73/4.99  --inst_passive_queues_freq              [25;2]
% 35.73/4.99  --inst_dismatching                      true
% 35.73/4.99  --inst_eager_unprocessed_to_passive     true
% 35.73/4.99  --inst_prop_sim_given                   true
% 35.73/4.99  --inst_prop_sim_new                     false
% 35.73/4.99  --inst_subs_new                         false
% 35.73/4.99  --inst_eq_res_simp                      false
% 35.73/4.99  --inst_subs_given                       false
% 35.73/4.99  --inst_orphan_elimination               true
% 35.73/4.99  --inst_learning_loop_flag               true
% 35.73/4.99  --inst_learning_start                   3000
% 35.73/4.99  --inst_learning_factor                  2
% 35.73/4.99  --inst_start_prop_sim_after_learn       3
% 35.73/4.99  --inst_sel_renew                        solver
% 35.73/4.99  --inst_lit_activity_flag                true
% 35.73/4.99  --inst_restr_to_given                   false
% 35.73/4.99  --inst_activity_threshold               500
% 35.73/4.99  --inst_out_proof                        true
% 35.73/4.99  
% 35.73/4.99  ------ Resolution Options
% 35.73/4.99  
% 35.73/4.99  --resolution_flag                       true
% 35.73/4.99  --res_lit_sel                           adaptive
% 35.73/4.99  --res_lit_sel_side                      none
% 35.73/4.99  --res_ordering                          kbo
% 35.73/4.99  --res_to_prop_solver                    active
% 35.73/4.99  --res_prop_simpl_new                    false
% 35.73/4.99  --res_prop_simpl_given                  true
% 35.73/4.99  --res_passive_queue_type                priority_queues
% 35.73/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.73/4.99  --res_passive_queues_freq               [15;5]
% 35.73/4.99  --res_forward_subs                      full
% 35.73/4.99  --res_backward_subs                     full
% 35.73/4.99  --res_forward_subs_resolution           true
% 35.73/4.99  --res_backward_subs_resolution          true
% 35.73/4.99  --res_orphan_elimination                true
% 35.73/4.99  --res_time_limit                        2.
% 35.73/4.99  --res_out_proof                         true
% 35.73/4.99  
% 35.73/4.99  ------ Superposition Options
% 35.73/4.99  
% 35.73/4.99  --superposition_flag                    true
% 35.73/4.99  --sup_passive_queue_type                priority_queues
% 35.73/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.73/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.73/4.99  --demod_completeness_check              fast
% 35.73/4.99  --demod_use_ground                      true
% 35.73/4.99  --sup_to_prop_solver                    passive
% 35.73/4.99  --sup_prop_simpl_new                    true
% 35.73/4.99  --sup_prop_simpl_given                  true
% 35.73/4.99  --sup_fun_splitting                     false
% 35.73/4.99  --sup_smt_interval                      50000
% 35.73/4.99  
% 35.73/4.99  ------ Superposition Simplification Setup
% 35.73/4.99  
% 35.73/4.99  --sup_indices_passive                   []
% 35.73/4.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.73/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_full_bw                           [BwDemod]
% 35.73/4.99  --sup_immed_triv                        [TrivRules]
% 35.73/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.73/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_immed_bw_main                     []
% 35.73/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.73/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.73/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.73/4.99  
% 35.73/4.99  ------ Combination Options
% 35.73/4.99  
% 35.73/4.99  --comb_res_mult                         3
% 35.73/4.99  --comb_sup_mult                         2
% 35.73/4.99  --comb_inst_mult                        10
% 35.73/4.99  
% 35.73/4.99  ------ Debug Options
% 35.73/4.99  
% 35.73/4.99  --dbg_backtrace                         false
% 35.73/4.99  --dbg_dump_prop_clauses                 false
% 35.73/4.99  --dbg_dump_prop_clauses_file            -
% 35.73/4.99  --dbg_out_stat                          false
% 35.73/4.99  ------ Parsing...
% 35.73/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.73/4.99  ------ Proving...
% 35.73/4.99  ------ Problem Properties 
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  clauses                                 13
% 35.73/4.99  conjectures                             3
% 35.73/4.99  EPR                                     2
% 35.73/4.99  Horn                                    13
% 35.73/4.99  unary                                   6
% 35.73/4.99  binary                                  2
% 35.73/4.99  lits                                    26
% 35.73/4.99  lits eq                                 3
% 35.73/4.99  fd_pure                                 0
% 35.73/4.99  fd_pseudo                               0
% 35.73/4.99  fd_cond                                 0
% 35.73/4.99  fd_pseudo_cond                          1
% 35.73/4.99  AC symbols                              0
% 35.73/4.99  
% 35.73/4.99  ------ Schedule dynamic 5 is on 
% 35.73/4.99  
% 35.73/4.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  ------ 
% 35.73/4.99  Current options:
% 35.73/4.99  ------ 
% 35.73/4.99  
% 35.73/4.99  ------ Input Options
% 35.73/4.99  
% 35.73/4.99  --out_options                           all
% 35.73/4.99  --tptp_safe_out                         true
% 35.73/4.99  --problem_path                          ""
% 35.73/4.99  --include_path                          ""
% 35.73/4.99  --clausifier                            res/vclausify_rel
% 35.73/4.99  --clausifier_options                    --mode clausify
% 35.73/4.99  --stdin                                 false
% 35.73/4.99  --stats_out                             all
% 35.73/4.99  
% 35.73/4.99  ------ General Options
% 35.73/4.99  
% 35.73/4.99  --fof                                   false
% 35.73/4.99  --time_out_real                         305.
% 35.73/4.99  --time_out_virtual                      -1.
% 35.73/4.99  --symbol_type_check                     false
% 35.73/4.99  --clausify_out                          false
% 35.73/4.99  --sig_cnt_out                           false
% 35.73/4.99  --trig_cnt_out                          false
% 35.73/4.99  --trig_cnt_out_tolerance                1.
% 35.73/4.99  --trig_cnt_out_sk_spl                   false
% 35.73/4.99  --abstr_cl_out                          false
% 35.73/4.99  
% 35.73/4.99  ------ Global Options
% 35.73/4.99  
% 35.73/4.99  --schedule                              default
% 35.73/4.99  --add_important_lit                     false
% 35.73/4.99  --prop_solver_per_cl                    1000
% 35.73/4.99  --min_unsat_core                        false
% 35.73/4.99  --soft_assumptions                      false
% 35.73/4.99  --soft_lemma_size                       3
% 35.73/4.99  --prop_impl_unit_size                   0
% 35.73/4.99  --prop_impl_unit                        []
% 35.73/4.99  --share_sel_clauses                     true
% 35.73/4.99  --reset_solvers                         false
% 35.73/4.99  --bc_imp_inh                            [conj_cone]
% 35.73/4.99  --conj_cone_tolerance                   3.
% 35.73/4.99  --extra_neg_conj                        none
% 35.73/4.99  --large_theory_mode                     true
% 35.73/4.99  --prolific_symb_bound                   200
% 35.73/4.99  --lt_threshold                          2000
% 35.73/4.99  --clause_weak_htbl                      true
% 35.73/4.99  --gc_record_bc_elim                     false
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing Options
% 35.73/4.99  
% 35.73/4.99  --preprocessing_flag                    true
% 35.73/4.99  --time_out_prep_mult                    0.1
% 35.73/4.99  --splitting_mode                        input
% 35.73/4.99  --splitting_grd                         true
% 35.73/4.99  --splitting_cvd                         false
% 35.73/4.99  --splitting_cvd_svl                     false
% 35.73/4.99  --splitting_nvd                         32
% 35.73/4.99  --sub_typing                            true
% 35.73/4.99  --prep_gs_sim                           true
% 35.73/4.99  --prep_unflatten                        true
% 35.73/4.99  --prep_res_sim                          true
% 35.73/4.99  --prep_upred                            true
% 35.73/4.99  --prep_sem_filter                       exhaustive
% 35.73/4.99  --prep_sem_filter_out                   false
% 35.73/4.99  --pred_elim                             true
% 35.73/4.99  --res_sim_input                         true
% 35.73/4.99  --eq_ax_congr_red                       true
% 35.73/4.99  --pure_diseq_elim                       true
% 35.73/4.99  --brand_transform                       false
% 35.73/4.99  --non_eq_to_eq                          false
% 35.73/4.99  --prep_def_merge                        true
% 35.73/4.99  --prep_def_merge_prop_impl              false
% 35.73/4.99  --prep_def_merge_mbd                    true
% 35.73/4.99  --prep_def_merge_tr_red                 false
% 35.73/4.99  --prep_def_merge_tr_cl                  false
% 35.73/4.99  --smt_preprocessing                     true
% 35.73/4.99  --smt_ac_axioms                         fast
% 35.73/4.99  --preprocessed_out                      false
% 35.73/4.99  --preprocessed_stats                    false
% 35.73/4.99  
% 35.73/4.99  ------ Abstraction refinement Options
% 35.73/4.99  
% 35.73/4.99  --abstr_ref                             []
% 35.73/4.99  --abstr_ref_prep                        false
% 35.73/4.99  --abstr_ref_until_sat                   false
% 35.73/4.99  --abstr_ref_sig_restrict                funpre
% 35.73/4.99  --abstr_ref_af_restrict_to_split_sk     false
% 35.73/4.99  --abstr_ref_under                       []
% 35.73/4.99  
% 35.73/4.99  ------ SAT Options
% 35.73/4.99  
% 35.73/4.99  --sat_mode                              false
% 35.73/4.99  --sat_fm_restart_options                ""
% 35.73/4.99  --sat_gr_def                            false
% 35.73/4.99  --sat_epr_types                         true
% 35.73/4.99  --sat_non_cyclic_types                  false
% 35.73/4.99  --sat_finite_models                     false
% 35.73/4.99  --sat_fm_lemmas                         false
% 35.73/4.99  --sat_fm_prep                           false
% 35.73/4.99  --sat_fm_uc_incr                        true
% 35.73/4.99  --sat_out_model                         small
% 35.73/4.99  --sat_out_clauses                       false
% 35.73/4.99  
% 35.73/4.99  ------ QBF Options
% 35.73/4.99  
% 35.73/4.99  --qbf_mode                              false
% 35.73/4.99  --qbf_elim_univ                         false
% 35.73/4.99  --qbf_dom_inst                          none
% 35.73/4.99  --qbf_dom_pre_inst                      false
% 35.73/4.99  --qbf_sk_in                             false
% 35.73/4.99  --qbf_pred_elim                         true
% 35.73/4.99  --qbf_split                             512
% 35.73/4.99  
% 35.73/4.99  ------ BMC1 Options
% 35.73/4.99  
% 35.73/4.99  --bmc1_incremental                      false
% 35.73/4.99  --bmc1_axioms                           reachable_all
% 35.73/4.99  --bmc1_min_bound                        0
% 35.73/4.99  --bmc1_max_bound                        -1
% 35.73/4.99  --bmc1_max_bound_default                -1
% 35.73/4.99  --bmc1_symbol_reachability              true
% 35.73/4.99  --bmc1_property_lemmas                  false
% 35.73/4.99  --bmc1_k_induction                      false
% 35.73/4.99  --bmc1_non_equiv_states                 false
% 35.73/4.99  --bmc1_deadlock                         false
% 35.73/4.99  --bmc1_ucm                              false
% 35.73/4.99  --bmc1_add_unsat_core                   none
% 35.73/4.99  --bmc1_unsat_core_children              false
% 35.73/4.99  --bmc1_unsat_core_extrapolate_axioms    false
% 35.73/4.99  --bmc1_out_stat                         full
% 35.73/4.99  --bmc1_ground_init                      false
% 35.73/4.99  --bmc1_pre_inst_next_state              false
% 35.73/4.99  --bmc1_pre_inst_state                   false
% 35.73/4.99  --bmc1_pre_inst_reach_state             false
% 35.73/4.99  --bmc1_out_unsat_core                   false
% 35.73/4.99  --bmc1_aig_witness_out                  false
% 35.73/4.99  --bmc1_verbose                          false
% 35.73/4.99  --bmc1_dump_clauses_tptp                false
% 35.73/4.99  --bmc1_dump_unsat_core_tptp             false
% 35.73/4.99  --bmc1_dump_file                        -
% 35.73/4.99  --bmc1_ucm_expand_uc_limit              128
% 35.73/4.99  --bmc1_ucm_n_expand_iterations          6
% 35.73/4.99  --bmc1_ucm_extend_mode                  1
% 35.73/4.99  --bmc1_ucm_init_mode                    2
% 35.73/4.99  --bmc1_ucm_cone_mode                    none
% 35.73/4.99  --bmc1_ucm_reduced_relation_type        0
% 35.73/4.99  --bmc1_ucm_relax_model                  4
% 35.73/4.99  --bmc1_ucm_full_tr_after_sat            true
% 35.73/4.99  --bmc1_ucm_expand_neg_assumptions       false
% 35.73/4.99  --bmc1_ucm_layered_model                none
% 35.73/4.99  --bmc1_ucm_max_lemma_size               10
% 35.73/4.99  
% 35.73/4.99  ------ AIG Options
% 35.73/4.99  
% 35.73/4.99  --aig_mode                              false
% 35.73/4.99  
% 35.73/4.99  ------ Instantiation Options
% 35.73/4.99  
% 35.73/4.99  --instantiation_flag                    true
% 35.73/4.99  --inst_sos_flag                         false
% 35.73/4.99  --inst_sos_phase                        true
% 35.73/4.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.73/4.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.73/4.99  --inst_lit_sel_side                     none
% 35.73/4.99  --inst_solver_per_active                1400
% 35.73/4.99  --inst_solver_calls_frac                1.
% 35.73/4.99  --inst_passive_queue_type               priority_queues
% 35.73/4.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.73/4.99  --inst_passive_queues_freq              [25;2]
% 35.73/4.99  --inst_dismatching                      true
% 35.73/4.99  --inst_eager_unprocessed_to_passive     true
% 35.73/4.99  --inst_prop_sim_given                   true
% 35.73/4.99  --inst_prop_sim_new                     false
% 35.73/4.99  --inst_subs_new                         false
% 35.73/4.99  --inst_eq_res_simp                      false
% 35.73/4.99  --inst_subs_given                       false
% 35.73/4.99  --inst_orphan_elimination               true
% 35.73/4.99  --inst_learning_loop_flag               true
% 35.73/4.99  --inst_learning_start                   3000
% 35.73/4.99  --inst_learning_factor                  2
% 35.73/4.99  --inst_start_prop_sim_after_learn       3
% 35.73/4.99  --inst_sel_renew                        solver
% 35.73/4.99  --inst_lit_activity_flag                true
% 35.73/4.99  --inst_restr_to_given                   false
% 35.73/4.99  --inst_activity_threshold               500
% 35.73/4.99  --inst_out_proof                        true
% 35.73/4.99  
% 35.73/4.99  ------ Resolution Options
% 35.73/4.99  
% 35.73/4.99  --resolution_flag                       false
% 35.73/4.99  --res_lit_sel                           adaptive
% 35.73/4.99  --res_lit_sel_side                      none
% 35.73/4.99  --res_ordering                          kbo
% 35.73/4.99  --res_to_prop_solver                    active
% 35.73/4.99  --res_prop_simpl_new                    false
% 35.73/4.99  --res_prop_simpl_given                  true
% 35.73/4.99  --res_passive_queue_type                priority_queues
% 35.73/4.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.73/4.99  --res_passive_queues_freq               [15;5]
% 35.73/4.99  --res_forward_subs                      full
% 35.73/4.99  --res_backward_subs                     full
% 35.73/4.99  --res_forward_subs_resolution           true
% 35.73/4.99  --res_backward_subs_resolution          true
% 35.73/4.99  --res_orphan_elimination                true
% 35.73/4.99  --res_time_limit                        2.
% 35.73/4.99  --res_out_proof                         true
% 35.73/4.99  
% 35.73/4.99  ------ Superposition Options
% 35.73/4.99  
% 35.73/4.99  --superposition_flag                    true
% 35.73/4.99  --sup_passive_queue_type                priority_queues
% 35.73/4.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.73/4.99  --sup_passive_queues_freq               [8;1;4]
% 35.73/4.99  --demod_completeness_check              fast
% 35.73/4.99  --demod_use_ground                      true
% 35.73/4.99  --sup_to_prop_solver                    passive
% 35.73/4.99  --sup_prop_simpl_new                    true
% 35.73/4.99  --sup_prop_simpl_given                  true
% 35.73/4.99  --sup_fun_splitting                     false
% 35.73/4.99  --sup_smt_interval                      50000
% 35.73/4.99  
% 35.73/4.99  ------ Superposition Simplification Setup
% 35.73/4.99  
% 35.73/4.99  --sup_indices_passive                   []
% 35.73/4.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.73/4.99  --sup_full_triv                         [TrivRules;PropSubs]
% 35.73/4.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_full_bw                           [BwDemod]
% 35.73/4.99  --sup_immed_triv                        [TrivRules]
% 35.73/4.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.73/4.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_immed_bw_main                     []
% 35.73/4.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.73/4.99  --sup_input_triv                        [Unflattening;TrivRules]
% 35.73/4.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.73/4.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.73/4.99  
% 35.73/4.99  ------ Combination Options
% 35.73/4.99  
% 35.73/4.99  --comb_res_mult                         3
% 35.73/4.99  --comb_sup_mult                         2
% 35.73/4.99  --comb_inst_mult                        10
% 35.73/4.99  
% 35.73/4.99  ------ Debug Options
% 35.73/4.99  
% 35.73/4.99  --dbg_backtrace                         false
% 35.73/4.99  --dbg_dump_prop_clauses                 false
% 35.73/4.99  --dbg_dump_prop_clauses_file            -
% 35.73/4.99  --dbg_out_stat                          false
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  ------ Proving...
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  % SZS status Theorem for theBenchmark.p
% 35.73/4.99  
% 35.73/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.73/4.99  
% 35.73/4.99  fof(f9,axiom,(
% 35.73/4.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f21,plain,(
% 35.73/4.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.73/4.99    inference(ennf_transformation,[],[f9])).
% 35.73/4.99  
% 35.73/4.99  fof(f22,plain,(
% 35.73/4.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.73/4.99    inference(flattening,[],[f21])).
% 35.73/4.99  
% 35.73/4.99  fof(f40,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f22])).
% 35.73/4.99  
% 35.73/4.99  fof(f10,conjecture,(
% 35.73/4.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f11,negated_conjecture,(
% 35.73/4.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 35.73/4.99    inference(negated_conjecture,[],[f10])).
% 35.73/4.99  
% 35.73/4.99  fof(f23,plain,(
% 35.73/4.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.73/4.99    inference(ennf_transformation,[],[f11])).
% 35.73/4.99  
% 35.73/4.99  fof(f28,plain,(
% 35.73/4.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.73/4.99    introduced(choice_axiom,[])).
% 35.73/4.99  
% 35.73/4.99  fof(f27,plain,(
% 35.73/4.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.73/4.99    introduced(choice_axiom,[])).
% 35.73/4.99  
% 35.73/4.99  fof(f26,plain,(
% 35.73/4.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 35.73/4.99    introduced(choice_axiom,[])).
% 35.73/4.99  
% 35.73/4.99  fof(f29,plain,(
% 35.73/4.99    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 35.73/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f28,f27,f26])).
% 35.73/4.99  
% 35.73/4.99  fof(f41,plain,(
% 35.73/4.99    l1_pre_topc(sK0)),
% 35.73/4.99    inference(cnf_transformation,[],[f29])).
% 35.73/4.99  
% 35.73/4.99  fof(f1,axiom,(
% 35.73/4.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f24,plain,(
% 35.73/4.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.73/4.99    inference(nnf_transformation,[],[f1])).
% 35.73/4.99  
% 35.73/4.99  fof(f25,plain,(
% 35.73/4.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.73/4.99    inference(flattening,[],[f24])).
% 35.73/4.99  
% 35.73/4.99  fof(f30,plain,(
% 35.73/4.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.73/4.99    inference(cnf_transformation,[],[f25])).
% 35.73/4.99  
% 35.73/4.99  fof(f46,plain,(
% 35.73/4.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.73/4.99    inference(equality_resolution,[],[f30])).
% 35.73/4.99  
% 35.73/4.99  fof(f3,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f12,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.73/4.99    inference(ennf_transformation,[],[f3])).
% 35.73/4.99  
% 35.73/4.99  fof(f34,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f12])).
% 35.73/4.99  
% 35.73/4.99  fof(f5,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f13,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.73/4.99    inference(ennf_transformation,[],[f5])).
% 35.73/4.99  
% 35.73/4.99  fof(f14,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.73/4.99    inference(flattening,[],[f13])).
% 35.73/4.99  
% 35.73/4.99  fof(f36,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f14])).
% 35.73/4.99  
% 35.73/4.99  fof(f4,axiom,(
% 35.73/4.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f35,plain,(
% 35.73/4.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.73/4.99    inference(cnf_transformation,[],[f4])).
% 35.73/4.99  
% 35.73/4.99  fof(f2,axiom,(
% 35.73/4.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f33,plain,(
% 35.73/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 35.73/4.99    inference(cnf_transformation,[],[f2])).
% 35.73/4.99  
% 35.73/4.99  fof(f42,plain,(
% 35.73/4.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.73/4.99    inference(cnf_transformation,[],[f29])).
% 35.73/4.99  
% 35.73/4.99  fof(f43,plain,(
% 35.73/4.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.73/4.99    inference(cnf_transformation,[],[f29])).
% 35.73/4.99  
% 35.73/4.99  fof(f7,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f17,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.73/4.99    inference(ennf_transformation,[],[f7])).
% 35.73/4.99  
% 35.73/4.99  fof(f18,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.73/4.99    inference(flattening,[],[f17])).
% 35.73/4.99  
% 35.73/4.99  fof(f38,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.73/4.99    inference(cnf_transformation,[],[f18])).
% 35.73/4.99  
% 35.73/4.99  fof(f6,axiom,(
% 35.73/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f15,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.73/4.99    inference(ennf_transformation,[],[f6])).
% 35.73/4.99  
% 35.73/4.99  fof(f16,plain,(
% 35.73/4.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.73/4.99    inference(flattening,[],[f15])).
% 35.73/4.99  
% 35.73/4.99  fof(f37,plain,(
% 35.73/4.99    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.73/4.99    inference(cnf_transformation,[],[f16])).
% 35.73/4.99  
% 35.73/4.99  fof(f8,axiom,(
% 35.73/4.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 35.73/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.73/4.99  
% 35.73/4.99  fof(f19,plain,(
% 35.73/4.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 35.73/4.99    inference(ennf_transformation,[],[f8])).
% 35.73/4.99  
% 35.73/4.99  fof(f20,plain,(
% 35.73/4.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 35.73/4.99    inference(flattening,[],[f19])).
% 35.73/4.99  
% 35.73/4.99  fof(f39,plain,(
% 35.73/4.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f20])).
% 35.73/4.99  
% 35.73/4.99  fof(f32,plain,(
% 35.73/4.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.73/4.99    inference(cnf_transformation,[],[f25])).
% 35.73/4.99  
% 35.73/4.99  fof(f44,plain,(
% 35.73/4.99    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 35.73/4.99    inference(cnf_transformation,[],[f29])).
% 35.73/4.99  
% 35.73/4.99  cnf(c_10,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.73/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.73/4.99      | ~ r1_tarski(X0,X2)
% 35.73/4.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 35.73/4.99      | ~ l1_pre_topc(X1) ),
% 35.73/4.99      inference(cnf_transformation,[],[f40]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_14,negated_conjecture,
% 35.73/4.99      ( l1_pre_topc(sK0) ),
% 35.73/4.99      inference(cnf_transformation,[],[f41]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_152,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.73/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.73/4.99      | ~ r1_tarski(X0,X2)
% 35.73/4.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 35.73/4.99      | sK0 != X1 ),
% 35.73/4.99      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_153,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ r1_tarski(X1,X0)
% 35.73/4.99      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 35.73/4.99      inference(unflattening,[status(thm)],[c_152]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_82893,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ r1_tarski(X0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
% 35.73/4.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_153]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_130530,plain,
% 35.73/4.99      ( ~ m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
% 35.73/4.99      | ~ r1_tarski(sK1,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_82893]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_2,plain,
% 35.73/4.99      ( r1_tarski(X0,X0) ),
% 35.73/4.99      inference(cnf_transformation,[],[f46]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_81414,plain,
% 35.73/4.99      ( r1_tarski(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,X0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_2]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_119843,plain,
% 35.73/4.99      ( r1_tarski(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_81414]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_277,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.73/4.99      theory(equality) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_75582,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,X1)
% 35.73/4.99      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_277]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_75915,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
% 35.73/4.99      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_75582]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_86342,plain,
% 35.73/4.99      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.73/4.99      | ~ r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(X2,X3))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0,X1)
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X2,X3) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_75915]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_88477,plain,
% 35.73/4.99      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.73/4.99      | ~ r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(X2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0,X1)
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_86342]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_113938,plain,
% 35.73/4.99      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.73/4.99      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_88477]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_113940,plain,
% 35.73/4.99      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.73/4.99      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_113938]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_281,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.73/4.99      theory(equality) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_76843,plain,
% 35.73/4.99      ( m1_subset_1(X0,X1)
% 35.73/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | X0 != X2
% 35.73/4.99      | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_281]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_79301,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | X1 != X0
% 35.73/4.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_76843]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_82500,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | k2_xboole_0(X1,X2) != X0
% 35.73/4.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_79301]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_87900,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)) != X0
% 35.73/4.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_82500]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_98588,plain,
% 35.73/4.99      ( m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)) != k2_xboole_0(sK1,sK2)
% 35.73/4.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_87900]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_4,plain,
% 35.73/4.99      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 35.73/4.99      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 35.73/4.99      inference(cnf_transformation,[],[f34]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_80240,plain,
% 35.73/4.99      ( ~ r1_tarski(k4_xboole_0(sK2,X0),X1)
% 35.73/4.99      | r1_tarski(sK2,k2_xboole_0(X0,X1)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_4]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_81413,plain,
% 35.73/4.99      ( ~ r1_tarski(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,X0))
% 35.73/4.99      | r1_tarski(sK2,k2_xboole_0(X0,k4_xboole_0(sK2,X0))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_80240]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_90822,plain,
% 35.73/4.99      ( ~ r1_tarski(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))
% 35.73/4.99      | r1_tarski(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_81413]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_6,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,X1)
% 35.73/4.99      | ~ r1_tarski(X2,X1)
% 35.73/4.99      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 35.73/4.99      inference(cnf_transformation,[],[f36]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_77111,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X0,X1))
% 35.73/4.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(X0,X1))
% 35.73/4.99      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_6]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_79318,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
% 35.73/4.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
% 35.73/4.99      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_77111]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_86480,plain,
% 35.73/4.99      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
% 35.73/4.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
% 35.73/4.99      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_79318]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_86479,plain,
% 35.73/4.99      ( ~ m1_subset_1(k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))))
% 35.73/4.99      | ~ r1_tarski(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_82893]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_5,plain,
% 35.73/4.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 35.73/4.99      inference(cnf_transformation,[],[f35]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_82357,plain,
% 35.73/4.99      ( r1_tarski(sK1,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_5]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_282,plain,
% 35.73/4.99      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 35.73/4.99      theory(equality) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_837,plain,
% 35.73/4.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 35.73/4.99      | sK0 != X1 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_282]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_56693,plain,
% 35.73/4.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
% 35.73/4.99      | sK0 != X0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_837]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_56694,plain,
% 35.73/4.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))
% 35.73/4.99      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)))
% 35.73/4.99      | sK0 != sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_56693]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_3,plain,
% 35.73/4.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 35.73/4.99      inference(cnf_transformation,[],[f33]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_29815,plain,
% 35.73/4.99      ( k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = k2_xboole_0(sK1,sK2) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_3]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_276,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_3786,plain,
% 35.73/4.99      ( X0 != X1
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = X0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_276]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_8012,plain,
% 35.73/4.99      ( X0 != k2_xboole_0(sK1,sK2)
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = X0
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_3786]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_29814,plain,
% 35.73/4.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK2,sK1))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 35.73/4.99      | k2_xboole_0(sK1,k4_xboole_0(sK2,sK1)) != k2_xboole_0(sK1,sK2) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_8012]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_13,negated_conjecture,
% 35.73/4.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.73/4.99      inference(cnf_transformation,[],[f42]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_493,plain,
% 35.73/4.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_12,negated_conjecture,
% 35.73/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.73/4.99      inference(cnf_transformation,[],[f43]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_494,plain,
% 35.73/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_8,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.73/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.73/4.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 35.73/4.99      inference(cnf_transformation,[],[f38]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_496,plain,
% 35.73/4.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 35.73/4.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 35.73/4.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_12071,plain,
% 35.73/4.99      ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
% 35.73/4.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_494,c_496]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_16710,plain,
% 35.73/4.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_493,c_12071]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_7,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.73/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.73/4.99      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 35.73/4.99      inference(cnf_transformation,[],[f37]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_497,plain,
% 35.73/4.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.73/4.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 35.73/4.99      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 35.73/4.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_17413,plain,
% 35.73/4.99      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 35.73/4.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.73/4.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.73/4.99      inference(superposition,[status(thm)],[c_16710,c_497]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_17468,plain,
% 35.73/4.99      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.73/4.99      inference(predicate_to_equality_rev,[status(thm)],[c_17413]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_641,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,k1_tops_1(sK0,sK2)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_8]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_5393,plain,
% 35.73/4.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_641]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_275,plain,( X0 = X0 ),theory(equality) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_4337,plain,
% 35.73/4.99      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_275]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_626,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_8]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_803,plain,
% 35.73/4.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_626]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_9,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.73/4.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.73/4.99      | ~ l1_pre_topc(X1) ),
% 35.73/4.99      inference(cnf_transformation,[],[f39]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_170,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.73/4.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.73/4.99      | sK0 != X1 ),
% 35.73/4.99      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_171,plain,
% 35.73/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.73/4.99      inference(unflattening,[status(thm)],[c_170]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_584,plain,
% 35.73/4.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_171]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_581,plain,
% 35.73/4.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.73/4.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_171]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_0,plain,
% 35.73/4.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.73/4.99      inference(cnf_transformation,[],[f32]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_44,plain,
% 35.73/4.99      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_0]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_40,plain,
% 35.73/4.99      ( r1_tarski(sK0,sK0) ),
% 35.73/4.99      inference(instantiation,[status(thm)],[c_2]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(c_11,negated_conjecture,
% 35.73/4.99      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 35.73/4.99      inference(cnf_transformation,[],[f44]) ).
% 35.73/4.99  
% 35.73/4.99  cnf(contradiction,plain,
% 35.73/4.99      ( $false ),
% 35.73/4.99      inference(minisat,
% 35.73/4.99                [status(thm)],
% 35.73/4.99                [c_130530,c_119843,c_113940,c_98588,c_90822,c_86480,
% 35.73/4.99                 c_86479,c_82357,c_56694,c_29815,c_29814,c_17468,c_5393,
% 35.73/4.99                 c_4337,c_803,c_584,c_581,c_44,c_40,c_11,c_12,c_13]) ).
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.73/4.99  
% 35.73/4.99  ------                               Statistics
% 35.73/4.99  
% 35.73/4.99  ------ General
% 35.73/4.99  
% 35.73/4.99  abstr_ref_over_cycles:                  0
% 35.73/4.99  abstr_ref_under_cycles:                 0
% 35.73/4.99  gc_basic_clause_elim:                   0
% 35.73/4.99  forced_gc_time:                         0
% 35.73/4.99  parsing_time:                           0.011
% 35.73/4.99  unif_index_cands_time:                  0.
% 35.73/4.99  unif_index_add_time:                    0.
% 35.73/4.99  orderings_time:                         0.
% 35.73/4.99  out_proof_time:                         0.013
% 35.73/4.99  total_time:                             4.359
% 35.73/4.99  num_of_symbols:                         43
% 35.73/4.99  num_of_terms:                           171032
% 35.73/4.99  
% 35.73/4.99  ------ Preprocessing
% 35.73/4.99  
% 35.73/4.99  num_of_splits:                          0
% 35.73/4.99  num_of_split_atoms:                     0
% 35.73/4.99  num_of_reused_defs:                     0
% 35.73/4.99  num_eq_ax_congr_red:                    9
% 35.73/4.99  num_of_sem_filtered_clauses:            1
% 35.73/4.99  num_of_subtypes:                        0
% 35.73/4.99  monotx_restored_types:                  0
% 35.73/4.99  sat_num_of_epr_types:                   0
% 35.73/4.99  sat_num_of_non_cyclic_types:            0
% 35.73/4.99  sat_guarded_non_collapsed_types:        0
% 35.73/4.99  num_pure_diseq_elim:                    0
% 35.73/4.99  simp_replaced_by:                       0
% 35.73/4.99  res_preprocessed:                       72
% 35.73/4.99  prep_upred:                             0
% 35.73/4.99  prep_unflattend:                        2
% 35.73/4.99  smt_new_axioms:                         0
% 35.73/4.99  pred_elim_cands:                        2
% 35.73/4.99  pred_elim:                              1
% 35.73/4.99  pred_elim_cl:                           1
% 35.73/4.99  pred_elim_cycles:                       3
% 35.73/4.99  merged_defs:                            0
% 35.73/4.99  merged_defs_ncl:                        0
% 35.73/4.99  bin_hyper_res:                          0
% 35.73/4.99  prep_cycles:                            4
% 35.73/4.99  pred_elim_time:                         0.001
% 35.73/4.99  splitting_time:                         0.
% 35.73/4.99  sem_filter_time:                        0.
% 35.73/4.99  monotx_time:                            0.
% 35.73/4.99  subtype_inf_time:                       0.
% 35.73/4.99  
% 35.73/4.99  ------ Problem properties
% 35.73/4.99  
% 35.73/4.99  clauses:                                13
% 35.73/4.99  conjectures:                            3
% 35.73/4.99  epr:                                    2
% 35.73/4.99  horn:                                   13
% 35.73/4.99  ground:                                 3
% 35.73/4.99  unary:                                  6
% 35.73/4.99  binary:                                 2
% 35.73/4.99  lits:                                   26
% 35.73/4.99  lits_eq:                                3
% 35.73/4.99  fd_pure:                                0
% 35.73/4.99  fd_pseudo:                              0
% 35.73/4.99  fd_cond:                                0
% 35.73/4.99  fd_pseudo_cond:                         1
% 35.73/4.99  ac_symbols:                             0
% 35.73/4.99  
% 35.73/4.99  ------ Propositional Solver
% 35.73/4.99  
% 35.73/4.99  prop_solver_calls:                      41
% 35.73/4.99  prop_fast_solver_calls:                 1892
% 35.73/4.99  smt_solver_calls:                       0
% 35.73/4.99  smt_fast_solver_calls:                  0
% 35.73/4.99  prop_num_of_clauses:                    36672
% 35.73/4.99  prop_preprocess_simplified:             46211
% 35.73/4.99  prop_fo_subsumed:                       72
% 35.73/4.99  prop_solver_time:                       0.
% 35.73/4.99  smt_solver_time:                        0.
% 35.73/4.99  smt_fast_solver_time:                   0.
% 35.73/4.99  prop_fast_solver_time:                  0.
% 35.73/4.99  prop_unsat_core_time:                   0.005
% 35.73/4.99  
% 35.73/4.99  ------ QBF
% 35.73/4.99  
% 35.73/4.99  qbf_q_res:                              0
% 35.73/4.99  qbf_num_tautologies:                    0
% 35.73/4.99  qbf_prep_cycles:                        0
% 35.73/4.99  
% 35.73/4.99  ------ BMC1
% 35.73/4.99  
% 35.73/4.99  bmc1_current_bound:                     -1
% 35.73/4.99  bmc1_last_solved_bound:                 -1
% 35.73/4.99  bmc1_unsat_core_size:                   -1
% 35.73/4.99  bmc1_unsat_core_parents_size:           -1
% 35.73/4.99  bmc1_merge_next_fun:                    0
% 35.73/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.73/4.99  
% 35.73/4.99  ------ Instantiation
% 35.73/4.99  
% 35.73/4.99  inst_num_of_clauses:                    3942
% 35.73/4.99  inst_num_in_passive:                    2027
% 35.73/4.99  inst_num_in_active:                     4234
% 35.73/4.99  inst_num_in_unprocessed:                608
% 35.73/4.99  inst_num_of_loops:                      4424
% 35.73/4.99  inst_num_of_learning_restarts:          1
% 35.73/4.99  inst_num_moves_active_passive:          182
% 35.73/4.99  inst_lit_activity:                      0
% 35.73/4.99  inst_lit_activity_moves:                3
% 35.73/4.99  inst_num_tautologies:                   0
% 35.73/4.99  inst_num_prop_implied:                  0
% 35.73/4.99  inst_num_existing_simplified:           0
% 35.73/4.99  inst_num_eq_res_simplified:             0
% 35.73/4.99  inst_num_child_elim:                    0
% 35.73/4.99  inst_num_of_dismatching_blockings:      17689
% 35.73/4.99  inst_num_of_non_proper_insts:           10590
% 35.73/4.99  inst_num_of_duplicates:                 0
% 35.73/4.99  inst_inst_num_from_inst_to_res:         0
% 35.73/4.99  inst_dismatching_checking_time:         0.
% 35.73/4.99  
% 35.73/4.99  ------ Resolution
% 35.73/4.99  
% 35.73/4.99  res_num_of_clauses:                     22
% 35.73/4.99  res_num_in_passive:                     22
% 35.73/4.99  res_num_in_active:                      0
% 35.73/4.99  res_num_of_loops:                       76
% 35.73/4.99  res_forward_subset_subsumed:            898
% 35.73/4.99  res_backward_subset_subsumed:           6
% 35.73/4.99  res_forward_subsumed:                   0
% 35.73/4.99  res_backward_subsumed:                  0
% 35.73/4.99  res_forward_subsumption_resolution:     0
% 35.73/4.99  res_backward_subsumption_resolution:    0
% 35.73/4.99  res_clause_to_clause_subsumption:       57932
% 35.73/4.99  res_orphan_elimination:                 0
% 35.73/4.99  res_tautology_del:                      331
% 35.73/4.99  res_num_eq_res_simplified:              0
% 35.73/4.99  res_num_sel_changes:                    0
% 35.73/4.99  res_moves_from_active_to_pass:          0
% 35.73/4.99  
% 35.73/4.99  ------ Superposition
% 35.73/4.99  
% 35.73/4.99  sup_time_total:                         0.
% 35.73/4.99  sup_time_generating:                    0.
% 35.73/4.99  sup_time_sim_full:                      0.
% 35.73/4.99  sup_time_sim_immed:                     0.
% 35.73/4.99  
% 35.73/4.99  sup_num_of_clauses:                     6394
% 35.73/4.99  sup_num_in_active:                      866
% 35.73/4.99  sup_num_in_passive:                     5528
% 35.73/4.99  sup_num_of_loops:                       884
% 35.73/4.99  sup_fw_superposition:                   2548
% 35.73/4.99  sup_bw_superposition:                   4708
% 35.73/4.99  sup_immediate_simplified:               3546
% 35.73/4.99  sup_given_eliminated:                   0
% 35.73/4.99  comparisons_done:                       0
% 35.73/4.99  comparisons_avoided:                    0
% 35.73/4.99  
% 35.73/4.99  ------ Simplifications
% 35.73/4.99  
% 35.73/4.99  
% 35.73/4.99  sim_fw_subset_subsumed:                 5
% 35.73/4.99  sim_bw_subset_subsumed:                 14
% 35.73/4.99  sim_fw_subsumed:                        25
% 35.73/4.99  sim_bw_subsumed:                        0
% 35.73/4.99  sim_fw_subsumption_res:                 17
% 35.73/4.99  sim_bw_subsumption_res:                 0
% 35.73/4.99  sim_tautology_del:                      0
% 35.73/4.99  sim_eq_tautology_del:                   95
% 35.73/4.99  sim_eq_res_simp:                        0
% 35.73/4.99  sim_fw_demodulated:                     2374
% 35.73/4.99  sim_bw_demodulated:                     16
% 35.73/4.99  sim_light_normalised:                   3295
% 35.73/4.99  sim_joinable_taut:                      0
% 35.73/4.99  sim_joinable_simp:                      0
% 35.73/4.99  sim_ac_normalised:                      0
% 35.73/4.99  sim_smt_subsumption:                    0
% 35.73/4.99  
%------------------------------------------------------------------------------
