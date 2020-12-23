%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:48 EST 2020

% Result     : Theorem 15.41s
% Output     : CNFRefutation 15.41s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 488 expanded)
%              Number of clauses        :  113 ( 247 expanded)
%              Number of leaves         :   15 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          :  385 (1408 expanded)
%              Number of equality atoms :  122 ( 200 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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

fof(f20,plain,
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

fof(f23,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22,f21,f20])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_86,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_87,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_86])).

cnf(c_107,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_87])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_248,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_107,c_228])).

cnf(c_294,plain,
    ( m1_subset_1(k4_subset_1(X0_39,X1_39,X2_39),k1_zfmisc_1(X0_39))
    | ~ r1_tarski(X1_39,X0_39)
    | ~ r1_tarski(X2_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_248])).

cnf(c_1706,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)),k1_tops_1(sK0,X0_39),X2_39),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))))
    | ~ r1_tarski(X2_39,k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)))
    | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_2343,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)),k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X2_39)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))))
    | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)))
    | ~ r1_tarski(k1_tops_1(sK0,X2_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))) ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_44948,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1))))
    | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_2343])).

cnf(c_44954,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1))))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_44948])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | r1_tarski(X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_703,plain,
    ( ~ m1_subset_1(k4_subset_1(X0_39,X1_39,X2_39),k1_zfmisc_1(X0_39))
    | r1_tarski(k4_subset_1(X0_39,X1_39,X2_39),X0_39) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_3446,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)),k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X2_39)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))))
    | r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)),k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X2_39)),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_22060,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1))))
    | r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39)),k1_tops_1(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_3446])).

cnf(c_22066,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1))))
    | r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_22060])).

cnf(c_308,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(X2_39,X3_39)
    | X2_39 != X0_39
    | X3_39 != X1_39 ),
    theory(equality)).

cnf(c_612,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_39 ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_638,plain,
    ( ~ r1_tarski(X0_39,k1_tops_1(sK0,X1_39))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X1_39) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_677,plain,
    ( ~ r1_tarski(k4_subset_1(X0_39,X1_39,X2_39),k1_tops_1(sK0,X3_39))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(X0_39,X1_39,X2_39)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X3_39) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_11311,plain,
    ( ~ r1_tarski(k4_subset_1(X0_39,X1_39,X2_39),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(X0_39,X1_39,X2_39)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_22059,plain,
    ( ~ r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39)),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_11311])).

cnf(c_22062,plain,
    ( ~ r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_22059])).

cnf(c_1697,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(k1_tops_1(sK0,X2_39),k1_tops_1(sK0,k2_xboole_0(X2_39,X3_39)))
    | X0_39 != k1_tops_1(sK0,X2_39)
    | X1_39 != k1_tops_1(sK0,k2_xboole_0(X2_39,X3_39)) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_2060,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_39),X1_39)
    | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X2_39)))
    | X1_39 != k1_tops_1(sK0,k2_xboole_0(X0_39,X2_39))
    | k1_tops_1(sK0,X0_39) != k1_tops_1(sK0,X0_39) ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_2571,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X1_39))
    | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X2_39)))
    | k1_tops_1(sK0,X0_39) != k1_tops_1(sK0,X0_39)
    | k1_tops_1(sK0,X1_39) != k1_tops_1(sK0,k2_xboole_0(X0_39,X2_39)) ),
    inference(instantiation,[status(thm)],[c_2060])).

cnf(c_6551,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2571])).

cnf(c_307,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_637,plain,
    ( X0_39 != X1_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = X0_39 ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_664,plain,
    ( X0_39 != k1_tops_1(sK0,X1_39)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = X0_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X1_39) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1230,plain,
    ( X0_39 != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = X0_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_1342,plain,
    ( k1_tops_1(sK0,X0_39) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,X0_39)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_6544,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK2,sK1))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_1,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_302,plain,
    ( r1_tarski(X0_39,k2_xboole_0(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_5075,plain,
    ( r1_tarski(X0_39,k2_xboole_0(X0_39,sK2)) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_5077,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5075])).

cnf(c_4290,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,X0_39)) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_4292,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_4290])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_154,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_154])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_39,X0_39)
    | r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) ),
    inference(subtyping,[status(esa)],[c_155])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(X0_39,X1_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_39,k2_xboole_0(X0_39,X1_39))
    | r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))) ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_4263,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,X0_39)) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_4265,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_4263])).

cnf(c_3944,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_676,plain,
    ( X0_39 != X1_39
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1_39
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_39 ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_1607,plain,
    ( X0_39 != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_39
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_3537,plain,
    ( k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_3542,plain,
    ( k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3537])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_108,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_87])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_108,c_228])).

cnf(c_293,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,X1_39)
    | k4_subset_1(X1_39,X0_39,X2_39) = k2_xboole_0(X0_39,X2_39) ),
    inference(subtyping,[status(esa)],[c_249])).

cnf(c_1852,plain,
    ( ~ r1_tarski(X0_39,k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)))
    | ~ r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)))
    | k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)),k1_tops_1(sK0,X1_39),X0_39) = k2_xboole_0(k1_tops_1(sK0,X1_39),X0_39) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_2357,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)))
    | ~ r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)))
    | k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)),k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) = k2_xboole_0(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_3535,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)))
    | k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2357])).

cnf(c_3539,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
    | k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3535])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_303,plain,
    ( k2_xboole_0(X0_39,X1_39) = k2_xboole_0(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2899,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_312,plain,
    ( X0_39 != X1_39
    | k1_tops_1(X0_41,X0_39) = k1_tops_1(X0_41,X1_39) ),
    theory(equality)).

cnf(c_1630,plain,
    ( X0_39 != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,X0_39) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_2722,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_1836,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_766,plain,
    ( X0_39 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_39
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1329,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_298,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_588,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_586,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) != iProver_top
    | r1_tarski(X0_39,X1_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_932,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_586])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_297,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_589,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_933,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_586])).

cnf(c_593,plain,
    ( k4_subset_1(X0_39,X1_39,X2_39) = k2_xboole_0(X1_39,X2_39)
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(X2_39,X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_1061,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_39,sK1) = k2_xboole_0(X0_39,sK1)
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_593])).

cnf(c_1265,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_932,c_1061])).

cnf(c_592,plain,
    ( m1_subset_1(k4_subset_1(X0_39,X1_39,X2_39),k1_zfmisc_1(X0_39)) = iProver_top
    | r1_tarski(X2_39,X0_39) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1313,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_592])).

cnf(c_1318,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1313])).

cnf(c_1060,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_39,sK2) = k2_xboole_0(X0_39,sK2)
    | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_593])).

cnf(c_1117,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_933,c_1060])).

cnf(c_1311,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_592])).

cnf(c_1316,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1311])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_172,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_172])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_173])).

cnf(c_1110,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_1067,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_764,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_39
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,X0_39) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_998,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_698,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0_39),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_950,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_751,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_700,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_695,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_696,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_692,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_338,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_305,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_319,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_317,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44954,c_22066,c_22062,c_6551,c_6544,c_5077,c_4292,c_4265,c_3944,c_3542,c_3539,c_2899,c_2722,c_1836,c_1329,c_1318,c_1316,c_1110,c_1067,c_998,c_950,c_751,c_700,c_696,c_695,c_692,c_338,c_319,c_317,c_8,c_9,c_13,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.41/2.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.41/2.52  
% 15.41/2.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.41/2.52  
% 15.41/2.52  ------  iProver source info
% 15.41/2.52  
% 15.41/2.52  git: date: 2020-06-30 10:37:57 +0100
% 15.41/2.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.41/2.52  git: non_committed_changes: false
% 15.41/2.52  git: last_make_outside_of_git: false
% 15.41/2.52  
% 15.41/2.52  ------ 
% 15.41/2.52  
% 15.41/2.52  ------ Input Options
% 15.41/2.52  
% 15.41/2.52  --out_options                           all
% 15.41/2.52  --tptp_safe_out                         true
% 15.41/2.52  --problem_path                          ""
% 15.41/2.52  --include_path                          ""
% 15.41/2.52  --clausifier                            res/vclausify_rel
% 15.41/2.52  --clausifier_options                    ""
% 15.41/2.52  --stdin                                 false
% 15.41/2.52  --stats_out                             all
% 15.41/2.52  
% 15.41/2.52  ------ General Options
% 15.41/2.52  
% 15.41/2.52  --fof                                   false
% 15.41/2.52  --time_out_real                         305.
% 15.41/2.52  --time_out_virtual                      -1.
% 15.41/2.52  --symbol_type_check                     false
% 15.41/2.52  --clausify_out                          false
% 15.41/2.52  --sig_cnt_out                           false
% 15.41/2.52  --trig_cnt_out                          false
% 15.41/2.52  --trig_cnt_out_tolerance                1.
% 15.41/2.52  --trig_cnt_out_sk_spl                   false
% 15.41/2.52  --abstr_cl_out                          false
% 15.41/2.52  
% 15.41/2.52  ------ Global Options
% 15.41/2.52  
% 15.41/2.52  --schedule                              default
% 15.41/2.52  --add_important_lit                     false
% 15.41/2.52  --prop_solver_per_cl                    1000
% 15.41/2.52  --min_unsat_core                        false
% 15.41/2.52  --soft_assumptions                      false
% 15.41/2.52  --soft_lemma_size                       3
% 15.41/2.52  --prop_impl_unit_size                   0
% 15.41/2.52  --prop_impl_unit                        []
% 15.41/2.52  --share_sel_clauses                     true
% 15.41/2.52  --reset_solvers                         false
% 15.41/2.52  --bc_imp_inh                            [conj_cone]
% 15.41/2.52  --conj_cone_tolerance                   3.
% 15.41/2.52  --extra_neg_conj                        none
% 15.41/2.52  --large_theory_mode                     true
% 15.41/2.52  --prolific_symb_bound                   200
% 15.41/2.52  --lt_threshold                          2000
% 15.41/2.52  --clause_weak_htbl                      true
% 15.41/2.52  --gc_record_bc_elim                     false
% 15.41/2.52  
% 15.41/2.52  ------ Preprocessing Options
% 15.41/2.52  
% 15.41/2.52  --preprocessing_flag                    true
% 15.41/2.52  --time_out_prep_mult                    0.1
% 15.41/2.52  --splitting_mode                        input
% 15.41/2.52  --splitting_grd                         true
% 15.41/2.52  --splitting_cvd                         false
% 15.41/2.52  --splitting_cvd_svl                     false
% 15.41/2.52  --splitting_nvd                         32
% 15.41/2.52  --sub_typing                            true
% 15.41/2.52  --prep_gs_sim                           true
% 15.41/2.52  --prep_unflatten                        true
% 15.41/2.52  --prep_res_sim                          true
% 15.41/2.52  --prep_upred                            true
% 15.41/2.52  --prep_sem_filter                       exhaustive
% 15.41/2.52  --prep_sem_filter_out                   false
% 15.41/2.52  --pred_elim                             true
% 15.41/2.52  --res_sim_input                         true
% 15.41/2.52  --eq_ax_congr_red                       true
% 15.41/2.52  --pure_diseq_elim                       true
% 15.41/2.52  --brand_transform                       false
% 15.41/2.52  --non_eq_to_eq                          false
% 15.41/2.52  --prep_def_merge                        true
% 15.41/2.52  --prep_def_merge_prop_impl              false
% 15.41/2.52  --prep_def_merge_mbd                    true
% 15.41/2.52  --prep_def_merge_tr_red                 false
% 15.41/2.52  --prep_def_merge_tr_cl                  false
% 15.41/2.52  --smt_preprocessing                     true
% 15.41/2.52  --smt_ac_axioms                         fast
% 15.41/2.52  --preprocessed_out                      false
% 15.41/2.52  --preprocessed_stats                    false
% 15.41/2.52  
% 15.41/2.52  ------ Abstraction refinement Options
% 15.41/2.52  
% 15.41/2.52  --abstr_ref                             []
% 15.41/2.52  --abstr_ref_prep                        false
% 15.41/2.52  --abstr_ref_until_sat                   false
% 15.41/2.52  --abstr_ref_sig_restrict                funpre
% 15.41/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.41/2.52  --abstr_ref_under                       []
% 15.41/2.52  
% 15.41/2.52  ------ SAT Options
% 15.41/2.52  
% 15.41/2.52  --sat_mode                              false
% 15.41/2.52  --sat_fm_restart_options                ""
% 15.41/2.52  --sat_gr_def                            false
% 15.41/2.52  --sat_epr_types                         true
% 15.41/2.52  --sat_non_cyclic_types                  false
% 15.41/2.52  --sat_finite_models                     false
% 15.41/2.52  --sat_fm_lemmas                         false
% 15.41/2.52  --sat_fm_prep                           false
% 15.41/2.52  --sat_fm_uc_incr                        true
% 15.41/2.52  --sat_out_model                         small
% 15.41/2.52  --sat_out_clauses                       false
% 15.41/2.52  
% 15.41/2.52  ------ QBF Options
% 15.41/2.52  
% 15.41/2.52  --qbf_mode                              false
% 15.41/2.52  --qbf_elim_univ                         false
% 15.41/2.52  --qbf_dom_inst                          none
% 15.41/2.52  --qbf_dom_pre_inst                      false
% 15.41/2.52  --qbf_sk_in                             false
% 15.41/2.52  --qbf_pred_elim                         true
% 15.41/2.52  --qbf_split                             512
% 15.41/2.52  
% 15.41/2.52  ------ BMC1 Options
% 15.41/2.52  
% 15.41/2.52  --bmc1_incremental                      false
% 15.41/2.52  --bmc1_axioms                           reachable_all
% 15.41/2.52  --bmc1_min_bound                        0
% 15.41/2.52  --bmc1_max_bound                        -1
% 15.41/2.52  --bmc1_max_bound_default                -1
% 15.41/2.52  --bmc1_symbol_reachability              true
% 15.41/2.52  --bmc1_property_lemmas                  false
% 15.41/2.52  --bmc1_k_induction                      false
% 15.41/2.52  --bmc1_non_equiv_states                 false
% 15.41/2.52  --bmc1_deadlock                         false
% 15.41/2.52  --bmc1_ucm                              false
% 15.41/2.52  --bmc1_add_unsat_core                   none
% 15.41/2.52  --bmc1_unsat_core_children              false
% 15.41/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.41/2.52  --bmc1_out_stat                         full
% 15.41/2.52  --bmc1_ground_init                      false
% 15.41/2.52  --bmc1_pre_inst_next_state              false
% 15.41/2.52  --bmc1_pre_inst_state                   false
% 15.41/2.52  --bmc1_pre_inst_reach_state             false
% 15.41/2.52  --bmc1_out_unsat_core                   false
% 15.41/2.52  --bmc1_aig_witness_out                  false
% 15.41/2.52  --bmc1_verbose                          false
% 15.41/2.52  --bmc1_dump_clauses_tptp                false
% 15.41/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.41/2.52  --bmc1_dump_file                        -
% 15.41/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.41/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.41/2.52  --bmc1_ucm_extend_mode                  1
% 15.41/2.52  --bmc1_ucm_init_mode                    2
% 15.41/2.52  --bmc1_ucm_cone_mode                    none
% 15.41/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.41/2.52  --bmc1_ucm_relax_model                  4
% 15.41/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.41/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.41/2.52  --bmc1_ucm_layered_model                none
% 15.41/2.52  --bmc1_ucm_max_lemma_size               10
% 15.41/2.52  
% 15.41/2.52  ------ AIG Options
% 15.41/2.52  
% 15.41/2.52  --aig_mode                              false
% 15.41/2.52  
% 15.41/2.52  ------ Instantiation Options
% 15.41/2.52  
% 15.41/2.52  --instantiation_flag                    true
% 15.41/2.52  --inst_sos_flag                         true
% 15.41/2.52  --inst_sos_phase                        true
% 15.41/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.41/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.41/2.52  --inst_lit_sel_side                     num_symb
% 15.41/2.52  --inst_solver_per_active                1400
% 15.41/2.52  --inst_solver_calls_frac                1.
% 15.41/2.52  --inst_passive_queue_type               priority_queues
% 15.41/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.41/2.52  --inst_passive_queues_freq              [25;2]
% 15.41/2.52  --inst_dismatching                      true
% 15.41/2.52  --inst_eager_unprocessed_to_passive     true
% 15.41/2.52  --inst_prop_sim_given                   true
% 15.41/2.52  --inst_prop_sim_new                     false
% 15.41/2.52  --inst_subs_new                         false
% 15.41/2.52  --inst_eq_res_simp                      false
% 15.41/2.52  --inst_subs_given                       false
% 15.41/2.52  --inst_orphan_elimination               true
% 15.41/2.52  --inst_learning_loop_flag               true
% 15.41/2.52  --inst_learning_start                   3000
% 15.41/2.52  --inst_learning_factor                  2
% 15.41/2.52  --inst_start_prop_sim_after_learn       3
% 15.41/2.52  --inst_sel_renew                        solver
% 15.41/2.52  --inst_lit_activity_flag                true
% 15.41/2.52  --inst_restr_to_given                   false
% 15.41/2.52  --inst_activity_threshold               500
% 15.41/2.52  --inst_out_proof                        true
% 15.41/2.52  
% 15.41/2.52  ------ Resolution Options
% 15.41/2.52  
% 15.41/2.52  --resolution_flag                       true
% 15.41/2.52  --res_lit_sel                           adaptive
% 15.41/2.52  --res_lit_sel_side                      none
% 15.41/2.52  --res_ordering                          kbo
% 15.41/2.52  --res_to_prop_solver                    active
% 15.41/2.52  --res_prop_simpl_new                    false
% 15.41/2.52  --res_prop_simpl_given                  true
% 15.41/2.52  --res_passive_queue_type                priority_queues
% 15.41/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.41/2.52  --res_passive_queues_freq               [15;5]
% 15.41/2.52  --res_forward_subs                      full
% 15.41/2.52  --res_backward_subs                     full
% 15.41/2.52  --res_forward_subs_resolution           true
% 15.41/2.52  --res_backward_subs_resolution          true
% 15.41/2.52  --res_orphan_elimination                true
% 15.41/2.52  --res_time_limit                        2.
% 15.41/2.52  --res_out_proof                         true
% 15.41/2.52  
% 15.41/2.52  ------ Superposition Options
% 15.41/2.52  
% 15.41/2.52  --superposition_flag                    true
% 15.41/2.52  --sup_passive_queue_type                priority_queues
% 15.41/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.41/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.41/2.52  --demod_completeness_check              fast
% 15.41/2.52  --demod_use_ground                      true
% 15.41/2.52  --sup_to_prop_solver                    passive
% 15.41/2.52  --sup_prop_simpl_new                    true
% 15.41/2.52  --sup_prop_simpl_given                  true
% 15.41/2.52  --sup_fun_splitting                     true
% 15.41/2.52  --sup_smt_interval                      50000
% 15.41/2.52  
% 15.41/2.52  ------ Superposition Simplification Setup
% 15.41/2.52  
% 15.41/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.41/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.41/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.41/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.41/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.41/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.41/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.41/2.52  --sup_immed_triv                        [TrivRules]
% 15.41/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.52  --sup_immed_bw_main                     []
% 15.41/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.41/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.41/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.52  --sup_input_bw                          []
% 15.41/2.52  
% 15.41/2.52  ------ Combination Options
% 15.41/2.52  
% 15.41/2.52  --comb_res_mult                         3
% 15.41/2.52  --comb_sup_mult                         2
% 15.41/2.52  --comb_inst_mult                        10
% 15.41/2.52  
% 15.41/2.52  ------ Debug Options
% 15.41/2.52  
% 15.41/2.52  --dbg_backtrace                         false
% 15.41/2.52  --dbg_dump_prop_clauses                 false
% 15.41/2.52  --dbg_dump_prop_clauses_file            -
% 15.41/2.52  --dbg_out_stat                          false
% 15.41/2.52  ------ Parsing...
% 15.41/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.41/2.52  
% 15.41/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.41/2.52  
% 15.41/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.41/2.52  
% 15.41/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.41/2.52  ------ Proving...
% 15.41/2.52  ------ Problem Properties 
% 15.41/2.52  
% 15.41/2.52  
% 15.41/2.52  clauses                                 11
% 15.41/2.52  conjectures                             3
% 15.41/2.52  EPR                                     0
% 15.41/2.52  Horn                                    11
% 15.41/2.52  unary                                   5
% 15.41/2.52  binary                                  3
% 15.41/2.52  lits                                    21
% 15.41/2.52  lits eq                                 2
% 15.41/2.52  fd_pure                                 0
% 15.41/2.52  fd_pseudo                               0
% 15.41/2.52  fd_cond                                 0
% 15.41/2.52  fd_pseudo_cond                          0
% 15.41/2.52  AC symbols                              0
% 15.41/2.52  
% 15.41/2.52  ------ Schedule dynamic 5 is on 
% 15.41/2.52  
% 15.41/2.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.41/2.52  
% 15.41/2.52  
% 15.41/2.52  ------ 
% 15.41/2.52  Current options:
% 15.41/2.52  ------ 
% 15.41/2.52  
% 15.41/2.52  ------ Input Options
% 15.41/2.52  
% 15.41/2.52  --out_options                           all
% 15.41/2.52  --tptp_safe_out                         true
% 15.41/2.52  --problem_path                          ""
% 15.41/2.52  --include_path                          ""
% 15.41/2.52  --clausifier                            res/vclausify_rel
% 15.41/2.52  --clausifier_options                    ""
% 15.41/2.52  --stdin                                 false
% 15.41/2.52  --stats_out                             all
% 15.41/2.52  
% 15.41/2.52  ------ General Options
% 15.41/2.52  
% 15.41/2.52  --fof                                   false
% 15.41/2.52  --time_out_real                         305.
% 15.41/2.52  --time_out_virtual                      -1.
% 15.41/2.52  --symbol_type_check                     false
% 15.41/2.52  --clausify_out                          false
% 15.41/2.52  --sig_cnt_out                           false
% 15.41/2.52  --trig_cnt_out                          false
% 15.41/2.52  --trig_cnt_out_tolerance                1.
% 15.41/2.52  --trig_cnt_out_sk_spl                   false
% 15.41/2.52  --abstr_cl_out                          false
% 15.41/2.52  
% 15.41/2.52  ------ Global Options
% 15.41/2.52  
% 15.41/2.52  --schedule                              default
% 15.41/2.52  --add_important_lit                     false
% 15.41/2.52  --prop_solver_per_cl                    1000
% 15.41/2.52  --min_unsat_core                        false
% 15.41/2.52  --soft_assumptions                      false
% 15.41/2.52  --soft_lemma_size                       3
% 15.41/2.52  --prop_impl_unit_size                   0
% 15.41/2.52  --prop_impl_unit                        []
% 15.41/2.52  --share_sel_clauses                     true
% 15.41/2.52  --reset_solvers                         false
% 15.41/2.52  --bc_imp_inh                            [conj_cone]
% 15.41/2.52  --conj_cone_tolerance                   3.
% 15.41/2.52  --extra_neg_conj                        none
% 15.41/2.52  --large_theory_mode                     true
% 15.41/2.52  --prolific_symb_bound                   200
% 15.41/2.52  --lt_threshold                          2000
% 15.41/2.52  --clause_weak_htbl                      true
% 15.41/2.52  --gc_record_bc_elim                     false
% 15.41/2.52  
% 15.41/2.52  ------ Preprocessing Options
% 15.41/2.52  
% 15.41/2.52  --preprocessing_flag                    true
% 15.41/2.52  --time_out_prep_mult                    0.1
% 15.41/2.52  --splitting_mode                        input
% 15.41/2.52  --splitting_grd                         true
% 15.41/2.52  --splitting_cvd                         false
% 15.41/2.52  --splitting_cvd_svl                     false
% 15.41/2.52  --splitting_nvd                         32
% 15.41/2.52  --sub_typing                            true
% 15.41/2.52  --prep_gs_sim                           true
% 15.41/2.52  --prep_unflatten                        true
% 15.41/2.52  --prep_res_sim                          true
% 15.41/2.52  --prep_upred                            true
% 15.41/2.52  --prep_sem_filter                       exhaustive
% 15.41/2.52  --prep_sem_filter_out                   false
% 15.41/2.52  --pred_elim                             true
% 15.41/2.52  --res_sim_input                         true
% 15.41/2.52  --eq_ax_congr_red                       true
% 15.41/2.52  --pure_diseq_elim                       true
% 15.41/2.52  --brand_transform                       false
% 15.41/2.52  --non_eq_to_eq                          false
% 15.41/2.52  --prep_def_merge                        true
% 15.41/2.52  --prep_def_merge_prop_impl              false
% 15.41/2.52  --prep_def_merge_mbd                    true
% 15.41/2.52  --prep_def_merge_tr_red                 false
% 15.41/2.52  --prep_def_merge_tr_cl                  false
% 15.41/2.52  --smt_preprocessing                     true
% 15.41/2.52  --smt_ac_axioms                         fast
% 15.41/2.52  --preprocessed_out                      false
% 15.41/2.52  --preprocessed_stats                    false
% 15.41/2.52  
% 15.41/2.52  ------ Abstraction refinement Options
% 15.41/2.52  
% 15.41/2.52  --abstr_ref                             []
% 15.41/2.52  --abstr_ref_prep                        false
% 15.41/2.52  --abstr_ref_until_sat                   false
% 15.41/2.52  --abstr_ref_sig_restrict                funpre
% 15.41/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.41/2.52  --abstr_ref_under                       []
% 15.41/2.52  
% 15.41/2.52  ------ SAT Options
% 15.41/2.52  
% 15.41/2.52  --sat_mode                              false
% 15.41/2.52  --sat_fm_restart_options                ""
% 15.41/2.52  --sat_gr_def                            false
% 15.41/2.52  --sat_epr_types                         true
% 15.41/2.52  --sat_non_cyclic_types                  false
% 15.41/2.52  --sat_finite_models                     false
% 15.41/2.52  --sat_fm_lemmas                         false
% 15.41/2.52  --sat_fm_prep                           false
% 15.41/2.52  --sat_fm_uc_incr                        true
% 15.41/2.52  --sat_out_model                         small
% 15.41/2.52  --sat_out_clauses                       false
% 15.41/2.52  
% 15.41/2.52  ------ QBF Options
% 15.41/2.52  
% 15.41/2.52  --qbf_mode                              false
% 15.41/2.52  --qbf_elim_univ                         false
% 15.41/2.52  --qbf_dom_inst                          none
% 15.41/2.52  --qbf_dom_pre_inst                      false
% 15.41/2.52  --qbf_sk_in                             false
% 15.41/2.52  --qbf_pred_elim                         true
% 15.41/2.52  --qbf_split                             512
% 15.41/2.52  
% 15.41/2.52  ------ BMC1 Options
% 15.41/2.52  
% 15.41/2.52  --bmc1_incremental                      false
% 15.41/2.52  --bmc1_axioms                           reachable_all
% 15.41/2.52  --bmc1_min_bound                        0
% 15.41/2.52  --bmc1_max_bound                        -1
% 15.41/2.52  --bmc1_max_bound_default                -1
% 15.41/2.52  --bmc1_symbol_reachability              true
% 15.41/2.52  --bmc1_property_lemmas                  false
% 15.41/2.52  --bmc1_k_induction                      false
% 15.41/2.52  --bmc1_non_equiv_states                 false
% 15.41/2.52  --bmc1_deadlock                         false
% 15.41/2.52  --bmc1_ucm                              false
% 15.41/2.52  --bmc1_add_unsat_core                   none
% 15.41/2.52  --bmc1_unsat_core_children              false
% 15.41/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.41/2.52  --bmc1_out_stat                         full
% 15.41/2.52  --bmc1_ground_init                      false
% 15.41/2.52  --bmc1_pre_inst_next_state              false
% 15.41/2.52  --bmc1_pre_inst_state                   false
% 15.41/2.52  --bmc1_pre_inst_reach_state             false
% 15.41/2.52  --bmc1_out_unsat_core                   false
% 15.41/2.52  --bmc1_aig_witness_out                  false
% 15.41/2.52  --bmc1_verbose                          false
% 15.41/2.52  --bmc1_dump_clauses_tptp                false
% 15.41/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.41/2.52  --bmc1_dump_file                        -
% 15.41/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.41/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.41/2.52  --bmc1_ucm_extend_mode                  1
% 15.41/2.52  --bmc1_ucm_init_mode                    2
% 15.41/2.52  --bmc1_ucm_cone_mode                    none
% 15.41/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.41/2.52  --bmc1_ucm_relax_model                  4
% 15.41/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.41/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.41/2.52  --bmc1_ucm_layered_model                none
% 15.41/2.52  --bmc1_ucm_max_lemma_size               10
% 15.41/2.52  
% 15.41/2.52  ------ AIG Options
% 15.41/2.52  
% 15.41/2.52  --aig_mode                              false
% 15.41/2.52  
% 15.41/2.52  ------ Instantiation Options
% 15.41/2.52  
% 15.41/2.52  --instantiation_flag                    true
% 15.41/2.52  --inst_sos_flag                         true
% 15.41/2.52  --inst_sos_phase                        true
% 15.41/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.41/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.41/2.52  --inst_lit_sel_side                     none
% 15.41/2.52  --inst_solver_per_active                1400
% 15.41/2.52  --inst_solver_calls_frac                1.
% 15.41/2.52  --inst_passive_queue_type               priority_queues
% 15.41/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.41/2.52  --inst_passive_queues_freq              [25;2]
% 15.41/2.52  --inst_dismatching                      true
% 15.41/2.52  --inst_eager_unprocessed_to_passive     true
% 15.41/2.52  --inst_prop_sim_given                   true
% 15.41/2.52  --inst_prop_sim_new                     false
% 15.41/2.52  --inst_subs_new                         false
% 15.41/2.52  --inst_eq_res_simp                      false
% 15.41/2.52  --inst_subs_given                       false
% 15.41/2.52  --inst_orphan_elimination               true
% 15.41/2.52  --inst_learning_loop_flag               true
% 15.41/2.52  --inst_learning_start                   3000
% 15.41/2.52  --inst_learning_factor                  2
% 15.41/2.52  --inst_start_prop_sim_after_learn       3
% 15.41/2.52  --inst_sel_renew                        solver
% 15.41/2.52  --inst_lit_activity_flag                true
% 15.41/2.52  --inst_restr_to_given                   false
% 15.41/2.52  --inst_activity_threshold               500
% 15.41/2.52  --inst_out_proof                        true
% 15.41/2.52  
% 15.41/2.52  ------ Resolution Options
% 15.41/2.52  
% 15.41/2.52  --resolution_flag                       false
% 15.41/2.52  --res_lit_sel                           adaptive
% 15.41/2.52  --res_lit_sel_side                      none
% 15.41/2.52  --res_ordering                          kbo
% 15.41/2.52  --res_to_prop_solver                    active
% 15.41/2.52  --res_prop_simpl_new                    false
% 15.41/2.52  --res_prop_simpl_given                  true
% 15.41/2.52  --res_passive_queue_type                priority_queues
% 15.41/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.41/2.52  --res_passive_queues_freq               [15;5]
% 15.41/2.52  --res_forward_subs                      full
% 15.41/2.52  --res_backward_subs                     full
% 15.41/2.52  --res_forward_subs_resolution           true
% 15.41/2.52  --res_backward_subs_resolution          true
% 15.41/2.52  --res_orphan_elimination                true
% 15.41/2.52  --res_time_limit                        2.
% 15.41/2.52  --res_out_proof                         true
% 15.41/2.52  
% 15.41/2.52  ------ Superposition Options
% 15.41/2.52  
% 15.41/2.52  --superposition_flag                    true
% 15.41/2.52  --sup_passive_queue_type                priority_queues
% 15.41/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.41/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.41/2.52  --demod_completeness_check              fast
% 15.41/2.52  --demod_use_ground                      true
% 15.41/2.52  --sup_to_prop_solver                    passive
% 15.41/2.52  --sup_prop_simpl_new                    true
% 15.41/2.52  --sup_prop_simpl_given                  true
% 15.41/2.52  --sup_fun_splitting                     true
% 15.41/2.52  --sup_smt_interval                      50000
% 15.41/2.52  
% 15.41/2.52  ------ Superposition Simplification Setup
% 15.41/2.52  
% 15.41/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.41/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.41/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.41/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.41/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.41/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.41/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.41/2.52  --sup_immed_triv                        [TrivRules]
% 15.41/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.52  --sup_immed_bw_main                     []
% 15.41/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.41/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.41/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.52  --sup_input_bw                          []
% 15.41/2.52  
% 15.41/2.52  ------ Combination Options
% 15.41/2.52  
% 15.41/2.52  --comb_res_mult                         3
% 15.41/2.52  --comb_sup_mult                         2
% 15.41/2.52  --comb_inst_mult                        10
% 15.41/2.52  
% 15.41/2.52  ------ Debug Options
% 15.41/2.52  
% 15.41/2.52  --dbg_backtrace                         false
% 15.41/2.52  --dbg_dump_prop_clauses                 false
% 15.41/2.52  --dbg_dump_prop_clauses_file            -
% 15.41/2.52  --dbg_out_stat                          false
% 15.41/2.52  
% 15.41/2.52  
% 15.41/2.52  
% 15.41/2.52  
% 15.41/2.52  ------ Proving...
% 15.41/2.52  
% 15.41/2.52  
% 15.41/2.52  % SZS status Theorem for theBenchmark.p
% 15.41/2.52  
% 15.41/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.41/2.52  
% 15.41/2.52  fof(f3,axiom,(
% 15.41/2.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 15.41/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.52  
% 15.41/2.52  fof(f10,plain,(
% 15.41/2.52    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 15.41/2.52    inference(ennf_transformation,[],[f3])).
% 15.41/2.52  
% 15.41/2.52  fof(f11,plain,(
% 15.41/2.52    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.41/2.52    inference(flattening,[],[f10])).
% 15.41/2.52  
% 15.41/2.52  fof(f26,plain,(
% 15.41/2.52    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.41/2.52    inference(cnf_transformation,[],[f11])).
% 15.41/2.52  
% 15.41/2.52  fof(f5,axiom,(
% 15.41/2.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.41/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.52  
% 15.41/2.52  fof(f19,plain,(
% 15.41/2.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.41/2.52    inference(nnf_transformation,[],[f5])).
% 15.41/2.52  
% 15.41/2.52  fof(f29,plain,(
% 15.41/2.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.41/2.52    inference(cnf_transformation,[],[f19])).
% 15.41/2.52  
% 15.41/2.52  fof(f28,plain,(
% 15.41/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.41/2.52    inference(cnf_transformation,[],[f19])).
% 15.41/2.52  
% 15.41/2.52  fof(f2,axiom,(
% 15.41/2.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.41/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.52  
% 15.41/2.52  fof(f25,plain,(
% 15.41/2.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.41/2.52    inference(cnf_transformation,[],[f2])).
% 15.41/2.52  
% 15.41/2.52  fof(f7,axiom,(
% 15.41/2.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 15.41/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.52  
% 15.41/2.52  fof(f16,plain,(
% 15.41/2.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.41/2.52    inference(ennf_transformation,[],[f7])).
% 15.41/2.52  
% 15.41/2.52  fof(f17,plain,(
% 15.41/2.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.41/2.52    inference(flattening,[],[f16])).
% 15.41/2.52  
% 15.41/2.52  fof(f31,plain,(
% 15.41/2.52    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.41/2.52    inference(cnf_transformation,[],[f17])).
% 15.41/2.52  
% 15.41/2.52  fof(f8,conjecture,(
% 15.41/2.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 15.41/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.52  
% 15.41/2.52  fof(f9,negated_conjecture,(
% 15.41/2.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 15.41/2.52    inference(negated_conjecture,[],[f8])).
% 15.41/2.52  
% 15.41/2.52  fof(f18,plain,(
% 15.41/2.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.41/2.52    inference(ennf_transformation,[],[f9])).
% 15.41/2.52  
% 15.41/2.52  fof(f22,plain,(
% 15.41/2.52    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.41/2.52    introduced(choice_axiom,[])).
% 15.41/2.52  
% 15.41/2.52  fof(f21,plain,(
% 15.41/2.52    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.41/2.52    introduced(choice_axiom,[])).
% 15.41/2.52  
% 15.41/2.52  fof(f20,plain,(
% 15.41/2.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 15.41/2.52    introduced(choice_axiom,[])).
% 15.41/2.52  
% 15.41/2.52  fof(f23,plain,(
% 15.41/2.52    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 15.41/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22,f21,f20])).
% 15.41/2.52  
% 15.41/2.52  fof(f32,plain,(
% 15.41/2.52    l1_pre_topc(sK0)),
% 15.41/2.52    inference(cnf_transformation,[],[f23])).
% 15.41/2.52  
% 15.41/2.52  fof(f4,axiom,(
% 15.41/2.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 15.41/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.52  
% 15.41/2.52  fof(f12,plain,(
% 15.41/2.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 15.41/2.52    inference(ennf_transformation,[],[f4])).
% 15.41/2.52  
% 15.41/2.52  fof(f13,plain,(
% 15.41/2.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.41/2.52    inference(flattening,[],[f12])).
% 15.41/2.52  
% 15.41/2.52  fof(f27,plain,(
% 15.41/2.52    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.41/2.52    inference(cnf_transformation,[],[f13])).
% 15.41/2.52  
% 15.41/2.52  fof(f1,axiom,(
% 15.41/2.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.41/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.52  
% 15.41/2.52  fof(f24,plain,(
% 15.41/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.41/2.52    inference(cnf_transformation,[],[f1])).
% 15.41/2.52  
% 15.41/2.52  fof(f34,plain,(
% 15.41/2.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.41/2.52    inference(cnf_transformation,[],[f23])).
% 15.41/2.52  
% 15.41/2.52  fof(f33,plain,(
% 15.41/2.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.41/2.52    inference(cnf_transformation,[],[f23])).
% 15.41/2.52  
% 15.41/2.52  fof(f6,axiom,(
% 15.41/2.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.41/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.52  
% 15.41/2.52  fof(f14,plain,(
% 15.41/2.52    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.41/2.52    inference(ennf_transformation,[],[f6])).
% 15.41/2.52  
% 15.41/2.52  fof(f15,plain,(
% 15.41/2.52    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.41/2.52    inference(flattening,[],[f14])).
% 15.41/2.52  
% 15.41/2.52  fof(f30,plain,(
% 15.41/2.52    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.41/2.52    inference(cnf_transformation,[],[f15])).
% 15.41/2.52  
% 15.41/2.52  fof(f35,plain,(
% 15.41/2.52    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 15.41/2.52    inference(cnf_transformation,[],[f23])).
% 15.41/2.52  
% 15.41/2.52  cnf(c_2,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.41/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.41/2.52      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 15.41/2.52      inference(cnf_transformation,[],[f26]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_4,plain,
% 15.41/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.41/2.52      inference(cnf_transformation,[],[f29]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_86,plain,
% 15.41/2.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.41/2.52      inference(prop_impl,[status(thm)],[c_4]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_87,plain,
% 15.41/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.41/2.52      inference(renaming,[status(thm)],[c_86]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_107,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.41/2.52      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
% 15.41/2.52      | ~ r1_tarski(X2,X1) ),
% 15.41/2.52      inference(bin_hyper_res,[status(thm)],[c_2,c_87]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_227,plain,
% 15.41/2.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.41/2.52      inference(prop_impl,[status(thm)],[c_4]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_228,plain,
% 15.41/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.41/2.52      inference(renaming,[status(thm)],[c_227]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_248,plain,
% 15.41/2.52      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 15.41/2.52      | ~ r1_tarski(X1,X0)
% 15.41/2.52      | ~ r1_tarski(X2,X0) ),
% 15.41/2.52      inference(bin_hyper_res,[status(thm)],[c_107,c_228]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_294,plain,
% 15.41/2.52      ( m1_subset_1(k4_subset_1(X0_39,X1_39,X2_39),k1_zfmisc_1(X0_39))
% 15.41/2.52      | ~ r1_tarski(X1_39,X0_39)
% 15.41/2.52      | ~ r1_tarski(X2_39,X0_39) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_248]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1706,plain,
% 15.41/2.52      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)),k1_tops_1(sK0,X0_39),X2_39),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))))
% 15.41/2.52      | ~ r1_tarski(X2_39,k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_294]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_2343,plain,
% 15.41/2.52      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)),k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X2_39)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X2_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_1706]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_44948,plain,
% 15.41/2.52      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1))))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK1))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_2343]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_44954,plain,
% 15.41/2.52      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1))))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK2,sK1))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_44948]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_5,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.41/2.52      inference(cnf_transformation,[],[f28]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_300,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
% 15.41/2.52      | r1_tarski(X0_39,X1_39) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_5]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_703,plain,
% 15.41/2.52      ( ~ m1_subset_1(k4_subset_1(X0_39,X1_39,X2_39),k1_zfmisc_1(X0_39))
% 15.41/2.52      | r1_tarski(k4_subset_1(X0_39,X1_39,X2_39),X0_39) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_300]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_3446,plain,
% 15.41/2.52      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)),k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X2_39)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))))
% 15.41/2.52      | r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39)),k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X2_39)),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_703]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_22060,plain,
% 15.41/2.52      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1))))
% 15.41/2.52      | r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39)),k1_tops_1(sK0,k2_xboole_0(sK2,sK1))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_3446]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_22066,plain,
% 15.41/2.52      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1))))
% 15.41/2.52      | r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_xboole_0(sK2,sK1))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_22060]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_308,plain,
% 15.41/2.52      ( ~ r1_tarski(X0_39,X1_39)
% 15.41/2.52      | r1_tarski(X2_39,X3_39)
% 15.41/2.52      | X2_39 != X0_39
% 15.41/2.52      | X3_39 != X1_39 ),
% 15.41/2.52      theory(equality) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_612,plain,
% 15.41/2.52      ( ~ r1_tarski(X0_39,X1_39)
% 15.41/2.52      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_39
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_39 ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_308]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_638,plain,
% 15.41/2.52      ( ~ r1_tarski(X0_39,k1_tops_1(sK0,X1_39))
% 15.41/2.52      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_39
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X1_39) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_612]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_677,plain,
% 15.41/2.52      ( ~ r1_tarski(k4_subset_1(X0_39,X1_39,X2_39),k1_tops_1(sK0,X3_39))
% 15.41/2.52      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(X0_39,X1_39,X2_39)
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X3_39) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_638]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_11311,plain,
% 15.41/2.52      ( ~ r1_tarski(k4_subset_1(X0_39,X1_39,X2_39),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(X0_39,X1_39,X2_39)
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_677]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_22059,plain,
% 15.41/2.52      ( ~ r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39)),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_39))
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_11311]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_22062,plain,
% 15.41/2.52      ( ~ r1_tarski(k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_22059]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1697,plain,
% 15.41/2.52      ( r1_tarski(X0_39,X1_39)
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X2_39),k1_tops_1(sK0,k2_xboole_0(X2_39,X3_39)))
% 15.41/2.52      | X0_39 != k1_tops_1(sK0,X2_39)
% 15.41/2.52      | X1_39 != k1_tops_1(sK0,k2_xboole_0(X2_39,X3_39)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_308]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_2060,plain,
% 15.41/2.52      ( r1_tarski(k1_tops_1(sK0,X0_39),X1_39)
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X2_39)))
% 15.41/2.52      | X1_39 != k1_tops_1(sK0,k2_xboole_0(X0_39,X2_39))
% 15.41/2.52      | k1_tops_1(sK0,X0_39) != k1_tops_1(sK0,X0_39) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_1697]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_2571,plain,
% 15.41/2.52      ( r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,X1_39))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X2_39)))
% 15.41/2.52      | k1_tops_1(sK0,X0_39) != k1_tops_1(sK0,X0_39)
% 15.41/2.52      | k1_tops_1(sK0,X1_39) != k1_tops_1(sK0,k2_xboole_0(X0_39,X2_39)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_2060]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_6551,plain,
% 15.41/2.52      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 15.41/2.52      | k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 15.41/2.52      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_2571]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_307,plain,
% 15.41/2.52      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 15.41/2.52      theory(equality) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_637,plain,
% 15.41/2.52      ( X0_39 != X1_39
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_39
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = X0_39 ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_307]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_664,plain,
% 15.41/2.52      ( X0_39 != k1_tops_1(sK0,X1_39)
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = X0_39
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X1_39) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_637]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1230,plain,
% 15.41/2.52      ( X0_39 != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = X0_39
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_664]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1342,plain,
% 15.41/2.52      ( k1_tops_1(sK0,X0_39) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,X0_39)
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_1230]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_6544,plain,
% 15.41/2.52      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK2,sK1))
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 15.41/2.52      | k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_1342]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1,plain,
% 15.41/2.52      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 15.41/2.52      inference(cnf_transformation,[],[f25]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_302,plain,
% 15.41/2.52      ( r1_tarski(X0_39,k2_xboole_0(X0_39,X1_39)) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_1]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_5075,plain,
% 15.41/2.52      ( r1_tarski(X0_39,k2_xboole_0(X0_39,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_302]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_5077,plain,
% 15.41/2.52      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_5075]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_4290,plain,
% 15.41/2.52      ( r1_tarski(sK2,k2_xboole_0(sK2,X0_39)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_302]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_4292,plain,
% 15.41/2.52      ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_4290]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_7,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.41/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.41/2.52      | ~ r1_tarski(X0,X2)
% 15.41/2.52      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 15.41/2.52      | ~ l1_pre_topc(X1) ),
% 15.41/2.52      inference(cnf_transformation,[],[f31]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_11,negated_conjecture,
% 15.41/2.52      ( l1_pre_topc(sK0) ),
% 15.41/2.52      inference(cnf_transformation,[],[f32]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_154,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.41/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.41/2.52      | ~ r1_tarski(X0,X2)
% 15.41/2.52      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 15.41/2.52      | sK0 != X1 ),
% 15.41/2.52      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_155,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ r1_tarski(X1,X0)
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 15.41/2.52      inference(unflattening,[status(thm)],[c_154]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_296,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ r1_tarski(X1_39,X0_39)
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_155]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_619,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ m1_subset_1(k2_xboole_0(X0_39,X1_39),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ r1_tarski(X0_39,k2_xboole_0(X0_39,X1_39))
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X0_39,X1_39))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_296]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_4263,plain,
% 15.41/2.52      ( ~ m1_subset_1(k2_xboole_0(sK2,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)))
% 15.41/2.52      | ~ r1_tarski(sK2,k2_xboole_0(sK2,X0_39)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_619]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_4265,plain,
% 15.41/2.52      ( ~ m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_4263]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_3944,plain,
% 15.41/2.52      ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 15.41/2.52      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_619]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_676,plain,
% 15.41/2.52      ( X0_39 != X1_39
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1_39
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_39 ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_307]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1607,plain,
% 15.41/2.52      ( X0_39 != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_39
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_676]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_3537,plain,
% 15.41/2.52      ( k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_1607]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_3542,plain,
% 15.41/2.52      ( k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_3537]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_3,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.41/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.41/2.52      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 15.41/2.52      inference(cnf_transformation,[],[f27]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_108,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.41/2.52      | ~ r1_tarski(X2,X1)
% 15.41/2.52      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 15.41/2.52      inference(bin_hyper_res,[status(thm)],[c_3,c_87]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_249,plain,
% 15.41/2.52      ( ~ r1_tarski(X0,X1)
% 15.41/2.52      | ~ r1_tarski(X2,X1)
% 15.41/2.52      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 15.41/2.52      inference(bin_hyper_res,[status(thm)],[c_108,c_228]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_293,plain,
% 15.41/2.52      ( ~ r1_tarski(X0_39,X1_39)
% 15.41/2.52      | ~ r1_tarski(X2_39,X1_39)
% 15.41/2.52      | k4_subset_1(X1_39,X0_39,X2_39) = k2_xboole_0(X0_39,X2_39) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_249]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1852,plain,
% 15.41/2.52      ( ~ r1_tarski(X0_39,k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)))
% 15.41/2.52      | k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)),k1_tops_1(sK0,X1_39),X0_39) = k2_xboole_0(k1_tops_1(sK0,X1_39),X0_39) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_293]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_2357,plain,
% 15.41/2.52      ( ~ r1_tarski(k1_tops_1(sK0,X0_39),k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)))
% 15.41/2.52      | k4_subset_1(k1_tops_1(sK0,k2_xboole_0(X1_39,X2_39)),k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) = k2_xboole_0(k1_tops_1(sK0,X1_39),k1_tops_1(sK0,X0_39)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_1852]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_3535,plain,
% 15.41/2.52      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)))
% 15.41/2.52      | k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,X0_39)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_2357]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_3539,plain,
% 15.41/2.52      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK2,sK1)))
% 15.41/2.52      | k4_subset_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK1)),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_3535]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_0,plain,
% 15.41/2.52      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.41/2.52      inference(cnf_transformation,[],[f24]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_303,plain,
% 15.41/2.52      ( k2_xboole_0(X0_39,X1_39) = k2_xboole_0(X1_39,X0_39) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_0]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_2899,plain,
% 15.41/2.52      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_303]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_312,plain,
% 15.41/2.52      ( X0_39 != X1_39
% 15.41/2.52      | k1_tops_1(X0_41,X0_39) = k1_tops_1(X0_41,X1_39) ),
% 15.41/2.52      theory(equality) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1630,plain,
% 15.41/2.52      ( X0_39 != k2_xboole_0(sK1,sK2)
% 15.41/2.52      | k1_tops_1(sK0,X0_39) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_312]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_2722,plain,
% 15.41/2.52      ( k1_tops_1(sK0,k2_xboole_0(sK2,sK1)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 15.41/2.52      | k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_1630]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1836,plain,
% 15.41/2.52      ( k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_303]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_766,plain,
% 15.41/2.52      ( X0_39 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_39
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_676]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1329,plain,
% 15.41/2.52      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 15.41/2.52      | k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_766]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_9,negated_conjecture,
% 15.41/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.41/2.52      inference(cnf_transformation,[],[f34]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_298,negated_conjecture,
% 15.41/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_9]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_588,plain,
% 15.41/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.41/2.52      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_586,plain,
% 15.41/2.52      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) != iProver_top
% 15.41/2.52      | r1_tarski(X0_39,X1_39) = iProver_top ),
% 15.41/2.52      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_932,plain,
% 15.41/2.52      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 15.41/2.52      inference(superposition,[status(thm)],[c_588,c_586]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_10,negated_conjecture,
% 15.41/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.41/2.52      inference(cnf_transformation,[],[f33]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_297,negated_conjecture,
% 15.41/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_10]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_589,plain,
% 15.41/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.41/2.52      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_933,plain,
% 15.41/2.52      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 15.41/2.52      inference(superposition,[status(thm)],[c_589,c_586]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_593,plain,
% 15.41/2.52      ( k4_subset_1(X0_39,X1_39,X2_39) = k2_xboole_0(X1_39,X2_39)
% 15.41/2.52      | r1_tarski(X1_39,X0_39) != iProver_top
% 15.41/2.52      | r1_tarski(X2_39,X0_39) != iProver_top ),
% 15.41/2.52      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1061,plain,
% 15.41/2.52      ( k4_subset_1(u1_struct_0(sK0),X0_39,sK1) = k2_xboole_0(X0_39,sK1)
% 15.41/2.52      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
% 15.41/2.52      inference(superposition,[status(thm)],[c_933,c_593]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1265,plain,
% 15.41/2.52      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
% 15.41/2.52      inference(superposition,[status(thm)],[c_932,c_1061]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_592,plain,
% 15.41/2.52      ( m1_subset_1(k4_subset_1(X0_39,X1_39,X2_39),k1_zfmisc_1(X0_39)) = iProver_top
% 15.41/2.52      | r1_tarski(X2_39,X0_39) != iProver_top
% 15.41/2.52      | r1_tarski(X1_39,X0_39) != iProver_top ),
% 15.41/2.52      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1313,plain,
% 15.41/2.52      ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.41/2.52      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
% 15.41/2.52      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 15.41/2.52      inference(superposition,[status(thm)],[c_1265,c_592]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1318,plain,
% 15.41/2.52      ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 15.41/2.52      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 15.41/2.52      inference(predicate_to_equality_rev,[status(thm)],[c_1313]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1060,plain,
% 15.41/2.52      ( k4_subset_1(u1_struct_0(sK0),X0_39,sK2) = k2_xboole_0(X0_39,sK2)
% 15.41/2.52      | r1_tarski(X0_39,u1_struct_0(sK0)) != iProver_top ),
% 15.41/2.52      inference(superposition,[status(thm)],[c_932,c_593]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1117,plain,
% 15.41/2.52      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 15.41/2.52      inference(superposition,[status(thm)],[c_933,c_1060]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1311,plain,
% 15.41/2.52      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.41/2.52      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
% 15.41/2.52      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 15.41/2.52      inference(superposition,[status(thm)],[c_1117,c_592]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1316,plain,
% 15.41/2.52      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 15.41/2.52      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 15.41/2.52      inference(predicate_to_equality_rev,[status(thm)],[c_1311]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_6,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.41/2.52      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.41/2.52      | ~ l1_pre_topc(X1) ),
% 15.41/2.52      inference(cnf_transformation,[],[f30]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_172,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.41/2.52      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.41/2.52      | sK0 != X1 ),
% 15.41/2.52      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_173,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.41/2.52      inference(unflattening,[status(thm)],[c_172]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_295,plain,
% 15.41/2.52      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | m1_subset_1(k1_tops_1(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.41/2.52      inference(subtyping,[status(esa)],[c_173]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1110,plain,
% 15.41/2.52      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_295]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_1067,plain,
% 15.41/2.52      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
% 15.41/2.52      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_1060]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_764,plain,
% 15.41/2.52      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_39
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,X0_39) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_312]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_998,plain,
% 15.41/2.52      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 15.41/2.52      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_764]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_698,plain,
% 15.41/2.52      ( ~ m1_subset_1(k1_tops_1(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,X0_39),u1_struct_0(sK0)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_300]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_950,plain,
% 15.41/2.52      ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_698]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_751,plain,
% 15.41/2.52      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 15.41/2.52      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 15.41/2.52      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_293]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_700,plain,
% 15.41/2.52      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_698]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_695,plain,
% 15.41/2.52      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_300]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_696,plain,
% 15.41/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.41/2.52      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 15.41/2.52      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_692,plain,
% 15.41/2.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_300]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_338,plain,
% 15.41/2.52      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 15.41/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_295]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_305,plain,( X0_39 = X0_39 ),theory(equality) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_319,plain,
% 15.41/2.52      ( sK1 = sK1 ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_305]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_317,plain,
% 15.41/2.52      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) | sK1 != sK1 ),
% 15.41/2.52      inference(instantiation,[status(thm)],[c_312]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_8,negated_conjecture,
% 15.41/2.52      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 15.41/2.52      inference(cnf_transformation,[],[f35]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(c_13,plain,
% 15.41/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.41/2.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.41/2.52  
% 15.41/2.52  cnf(contradiction,plain,
% 15.41/2.52      ( $false ),
% 15.41/2.52      inference(minisat,
% 15.41/2.52                [status(thm)],
% 15.41/2.52                [c_44954,c_22066,c_22062,c_6551,c_6544,c_5077,c_4292,
% 15.41/2.52                 c_4265,c_3944,c_3542,c_3539,c_2899,c_2722,c_1836,c_1329,
% 15.41/2.52                 c_1318,c_1316,c_1110,c_1067,c_998,c_950,c_751,c_700,
% 15.41/2.52                 c_696,c_695,c_692,c_338,c_319,c_317,c_8,c_9,c_13,c_10]) ).
% 15.41/2.52  
% 15.41/2.52  
% 15.41/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.41/2.52  
% 15.41/2.52  ------                               Statistics
% 15.41/2.52  
% 15.41/2.52  ------ General
% 15.41/2.52  
% 15.41/2.52  abstr_ref_over_cycles:                  0
% 15.41/2.52  abstr_ref_under_cycles:                 0
% 15.41/2.52  gc_basic_clause_elim:                   0
% 15.41/2.52  forced_gc_time:                         0
% 15.41/2.52  parsing_time:                           0.01
% 15.41/2.52  unif_index_cands_time:                  0.
% 15.41/2.52  unif_index_add_time:                    0.
% 15.41/2.52  orderings_time:                         0.
% 15.41/2.52  out_proof_time:                         0.012
% 15.41/2.52  total_time:                             1.701
% 15.41/2.52  num_of_symbols:                         45
% 15.41/2.52  num_of_terms:                           63475
% 15.41/2.52  
% 15.41/2.52  ------ Preprocessing
% 15.41/2.52  
% 15.41/2.52  num_of_splits:                          0
% 15.41/2.52  num_of_split_atoms:                     0
% 15.41/2.52  num_of_reused_defs:                     0
% 15.41/2.52  num_eq_ax_congr_red:                    8
% 15.41/2.52  num_of_sem_filtered_clauses:            1
% 15.41/2.52  num_of_subtypes:                        3
% 15.41/2.52  monotx_restored_types:                  0
% 15.41/2.52  sat_num_of_epr_types:                   0
% 15.41/2.52  sat_num_of_non_cyclic_types:            0
% 15.41/2.52  sat_guarded_non_collapsed_types:        0
% 15.41/2.52  num_pure_diseq_elim:                    0
% 15.41/2.52  simp_replaced_by:                       0
% 15.41/2.52  res_preprocessed:                       62
% 15.41/2.52  prep_upred:                             0
% 15.41/2.52  prep_unflattend:                        2
% 15.41/2.52  smt_new_axioms:                         0
% 15.41/2.52  pred_elim_cands:                        2
% 15.41/2.52  pred_elim:                              1
% 15.41/2.52  pred_elim_cl:                           1
% 15.41/2.52  pred_elim_cycles:                       3
% 15.41/2.52  merged_defs:                            8
% 15.41/2.52  merged_defs_ncl:                        0
% 15.41/2.52  bin_hyper_res:                          12
% 15.41/2.52  prep_cycles:                            4
% 15.41/2.52  pred_elim_time:                         0.001
% 15.41/2.52  splitting_time:                         0.
% 15.41/2.52  sem_filter_time:                        0.
% 15.41/2.52  monotx_time:                            0.
% 15.41/2.52  subtype_inf_time:                       0.
% 15.41/2.52  
% 15.41/2.52  ------ Problem properties
% 15.41/2.52  
% 15.41/2.52  clauses:                                11
% 15.41/2.52  conjectures:                            3
% 15.41/2.52  epr:                                    0
% 15.41/2.52  horn:                                   11
% 15.41/2.52  ground:                                 3
% 15.41/2.52  unary:                                  5
% 15.41/2.52  binary:                                 3
% 15.41/2.52  lits:                                   21
% 15.41/2.52  lits_eq:                                2
% 15.41/2.52  fd_pure:                                0
% 15.41/2.52  fd_pseudo:                              0
% 15.41/2.52  fd_cond:                                0
% 15.41/2.52  fd_pseudo_cond:                         0
% 15.41/2.52  ac_symbols:                             0
% 15.41/2.52  
% 15.41/2.52  ------ Propositional Solver
% 15.41/2.52  
% 15.41/2.52  prop_solver_calls:                      36
% 15.41/2.52  prop_fast_solver_calls:                 1116
% 15.41/2.52  smt_solver_calls:                       0
% 15.41/2.52  smt_fast_solver_calls:                  0
% 15.41/2.52  prop_num_of_clauses:                    20487
% 15.41/2.52  prop_preprocess_simplified:             35959
% 15.41/2.52  prop_fo_subsumed:                       57
% 15.41/2.52  prop_solver_time:                       0.
% 15.41/2.52  smt_solver_time:                        0.
% 15.41/2.52  smt_fast_solver_time:                   0.
% 15.41/2.52  prop_fast_solver_time:                  0.
% 15.41/2.52  prop_unsat_core_time:                   0.002
% 15.41/2.52  
% 15.41/2.52  ------ QBF
% 15.41/2.52  
% 15.41/2.52  qbf_q_res:                              0
% 15.41/2.52  qbf_num_tautologies:                    0
% 15.41/2.52  qbf_prep_cycles:                        0
% 15.41/2.52  
% 15.41/2.52  ------ BMC1
% 15.41/2.52  
% 15.41/2.52  bmc1_current_bound:                     -1
% 15.41/2.52  bmc1_last_solved_bound:                 -1
% 15.41/2.52  bmc1_unsat_core_size:                   -1
% 15.41/2.52  bmc1_unsat_core_parents_size:           -1
% 15.41/2.52  bmc1_merge_next_fun:                    0
% 15.41/2.52  bmc1_unsat_core_clauses_time:           0.
% 15.41/2.52  
% 15.41/2.52  ------ Instantiation
% 15.41/2.52  
% 15.41/2.52  inst_num_of_clauses:                    4864
% 15.41/2.52  inst_num_in_passive:                    2483
% 15.41/2.52  inst_num_in_active:                     1987
% 15.41/2.52  inst_num_in_unprocessed:                395
% 15.41/2.52  inst_num_of_loops:                      2153
% 15.41/2.52  inst_num_of_learning_restarts:          0
% 15.41/2.52  inst_num_moves_active_passive:          159
% 15.41/2.52  inst_lit_activity:                      0
% 15.41/2.52  inst_lit_activity_moves:                0
% 15.41/2.52  inst_num_tautologies:                   0
% 15.41/2.52  inst_num_prop_implied:                  0
% 15.41/2.52  inst_num_existing_simplified:           0
% 15.41/2.52  inst_num_eq_res_simplified:             0
% 15.41/2.52  inst_num_child_elim:                    0
% 15.41/2.52  inst_num_of_dismatching_blockings:      6915
% 15.41/2.52  inst_num_of_non_proper_insts:           8375
% 15.41/2.52  inst_num_of_duplicates:                 0
% 15.41/2.52  inst_inst_num_from_inst_to_res:         0
% 15.41/2.52  inst_dismatching_checking_time:         0.
% 15.41/2.52  
% 15.41/2.52  ------ Resolution
% 15.41/2.52  
% 15.41/2.52  res_num_of_clauses:                     0
% 15.41/2.52  res_num_in_passive:                     0
% 15.41/2.52  res_num_in_active:                      0
% 15.41/2.52  res_num_of_loops:                       66
% 15.41/2.52  res_forward_subset_subsumed:            609
% 15.41/2.52  res_backward_subset_subsumed:           16
% 15.41/2.52  res_forward_subsumed:                   0
% 15.41/2.52  res_backward_subsumed:                  0
% 15.41/2.52  res_forward_subsumption_resolution:     0
% 15.41/2.52  res_backward_subsumption_resolution:    0
% 15.41/2.52  res_clause_to_clause_subsumption:       20105
% 15.41/2.52  res_orphan_elimination:                 0
% 15.41/2.52  res_tautology_del:                      605
% 15.41/2.52  res_num_eq_res_simplified:              0
% 15.41/2.52  res_num_sel_changes:                    0
% 15.41/2.52  res_moves_from_active_to_pass:          0
% 15.41/2.52  
% 15.41/2.52  ------ Superposition
% 15.41/2.52  
% 15.41/2.52  sup_time_total:                         0.
% 15.41/2.52  sup_time_generating:                    0.
% 15.41/2.52  sup_time_sim_full:                      0.
% 15.41/2.52  sup_time_sim_immed:                     0.
% 15.41/2.52  
% 15.41/2.52  sup_num_of_clauses:                     3848
% 15.41/2.52  sup_num_in_active:                      363
% 15.41/2.52  sup_num_in_passive:                     3485
% 15.41/2.52  sup_num_of_loops:                       430
% 15.41/2.52  sup_fw_superposition:                   2544
% 15.41/2.52  sup_bw_superposition:                   2309
% 15.41/2.52  sup_immediate_simplified:               1058
% 15.41/2.52  sup_given_eliminated:                   38
% 15.41/2.52  comparisons_done:                       0
% 15.41/2.52  comparisons_avoided:                    0
% 15.41/2.52  
% 15.41/2.52  ------ Simplifications
% 15.41/2.52  
% 15.41/2.52  
% 15.41/2.52  sim_fw_subset_subsumed:                 90
% 15.41/2.52  sim_bw_subset_subsumed:                 35
% 15.41/2.52  sim_fw_subsumed:                        364
% 15.41/2.52  sim_bw_subsumed:                        0
% 15.41/2.52  sim_fw_subsumption_res:                 0
% 15.41/2.52  sim_bw_subsumption_res:                 0
% 15.41/2.52  sim_tautology_del:                      1
% 15.41/2.52  sim_eq_tautology_del:                   33
% 15.41/2.52  sim_eq_res_simp:                        0
% 15.41/2.52  sim_fw_demodulated:                     132
% 15.41/2.52  sim_bw_demodulated:                     156
% 15.41/2.52  sim_light_normalised:                   796
% 15.41/2.52  sim_joinable_taut:                      0
% 15.41/2.52  sim_joinable_simp:                      0
% 15.41/2.52  sim_ac_normalised:                      0
% 15.41/2.52  sim_smt_subsumption:                    0
% 15.41/2.52  
%------------------------------------------------------------------------------
