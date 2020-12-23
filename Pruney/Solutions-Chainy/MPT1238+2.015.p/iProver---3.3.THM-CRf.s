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
% DateTime   : Thu Dec  3 12:13:49 EST 2020

% Result     : Theorem 31.77s
% Output     : CNFRefutation 31.77s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 406 expanded)
%              Number of clauses        :  104 ( 180 expanded)
%              Number of leaves         :   17 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :  368 (1194 expanded)
%              Number of equality atoms :  157 ( 235 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f26,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_97627,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_97965,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_97627])).

cnf(c_98453,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_97965])).

cnf(c_137113,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_98453])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_628,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1306,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_631])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_629,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1305,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_631])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_633,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_635,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2256,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_635])).

cnf(c_20149,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),u1_struct_0(sK0)) = u1_struct_0(sK0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_2256])).

cnf(c_22970,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK1),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1306,c_20149])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_634,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1207,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_634,c_635])).

cnf(c_4589,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1207])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_636,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1772,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_636])).

cnf(c_1800,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_1772])).

cnf(c_7348,plain,
    ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4589,c_1800])).

cnf(c_23060,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22970,c_7348])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_627,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_181])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_632,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20151,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,X0),X1),k1_tops_1(sK0,X2)) = k1_tops_1(sK0,X2)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,k1_tops_1(sK0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_2256])).

cnf(c_27999,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_20151])).

cnf(c_28475,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_27999])).

cnf(c_29611,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_28475])).

cnf(c_32858,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_29611])).

cnf(c_673,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_674,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_33015,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32858,c_674])).

cnf(c_91382,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23060,c_33015])).

cnf(c_333,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1282,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_6920,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6921,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6920])).

cnf(c_6923,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6924,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6923])).

cnf(c_40120,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4869,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k2_xboole_0(X2,X3))
    | X0 != X2
    | X1 != k2_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_10561,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
    | r1_tarski(X2,k2_xboole_0(X1,X0))
    | X2 != X0
    | k2_xboole_0(X1,X0) != k2_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_4869])).

cnf(c_18102,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1))
    | X0 != sK2
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_10561])).

cnf(c_73128,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1))
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_18102])).

cnf(c_73129,plain,
    ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1)
    | sK2 != sK2
    | r1_tarski(sK2,k2_xboole_0(sK2,sK1)) != iProver_top
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73128])).

cnf(c_91702,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_91382,c_1282,c_6921,c_6924,c_40120,c_73129])).

cnf(c_91773,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_91702,c_634])).

cnf(c_92023,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_91773])).

cnf(c_737,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_20943,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_752,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_struct_0(sK0))
    | X2 != X0
    | u1_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_1163,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | r1_tarski(X1,u1_struct_0(sK0))
    | X1 != X0
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_1566,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | X0 != sK1
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_1848,plain,
    ( r1_tarski(k2_xboole_0(X0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k2_xboole_0(X0,sK1) != sK1
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_7033,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k2_xboole_0(k1_tops_1(sK0,sK1),sK1) != sK1
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_4027,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_1561,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | X0 != sK2
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_1841,plain,
    ( r1_tarski(k2_xboole_0(X0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k2_xboole_0(X0,sK2) != sK2
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_3033,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k2_xboole_0(k1_tops_1(sK0,sK2),sK2) != sK2
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1841])).

cnf(c_339,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_1149,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_1555,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_1556,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_104,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_104])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_105])).

cnf(c_261,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_261])).

cnf(c_284,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_128,c_262])).

cnf(c_625,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_1311,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_625])).

cnf(c_1531,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1306,c_1311])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_626,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_889,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_626])).

cnf(c_1210,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_889,c_635])).

cnf(c_888,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_626])).

cnf(c_1209,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_888,c_635])).

cnf(c_1111,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_911,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_908,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_348,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_340,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_346,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_137113,c_92023,c_20943,c_7033,c_4027,c_3033,c_1556,c_1531,c_1210,c_1209,c_1111,c_911,c_908,c_348,c_346,c_10,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:50:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 31.77/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.77/4.49  
% 31.77/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.77/4.49  
% 31.77/4.49  ------  iProver source info
% 31.77/4.49  
% 31.77/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.77/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.77/4.49  git: non_committed_changes: false
% 31.77/4.49  git: last_make_outside_of_git: false
% 31.77/4.49  
% 31.77/4.49  ------ 
% 31.77/4.49  
% 31.77/4.49  ------ Input Options
% 31.77/4.49  
% 31.77/4.49  --out_options                           all
% 31.77/4.49  --tptp_safe_out                         true
% 31.77/4.49  --problem_path                          ""
% 31.77/4.49  --include_path                          ""
% 31.77/4.49  --clausifier                            res/vclausify_rel
% 31.77/4.49  --clausifier_options                    ""
% 31.77/4.49  --stdin                                 false
% 31.77/4.49  --stats_out                             all
% 31.77/4.49  
% 31.77/4.49  ------ General Options
% 31.77/4.49  
% 31.77/4.49  --fof                                   false
% 31.77/4.49  --time_out_real                         305.
% 31.77/4.49  --time_out_virtual                      -1.
% 31.77/4.49  --symbol_type_check                     false
% 31.77/4.49  --clausify_out                          false
% 31.77/4.49  --sig_cnt_out                           false
% 31.77/4.49  --trig_cnt_out                          false
% 31.77/4.49  --trig_cnt_out_tolerance                1.
% 31.77/4.49  --trig_cnt_out_sk_spl                   false
% 31.77/4.49  --abstr_cl_out                          false
% 31.77/4.49  
% 31.77/4.49  ------ Global Options
% 31.77/4.49  
% 31.77/4.49  --schedule                              default
% 31.77/4.49  --add_important_lit                     false
% 31.77/4.49  --prop_solver_per_cl                    1000
% 31.77/4.49  --min_unsat_core                        false
% 31.77/4.49  --soft_assumptions                      false
% 31.77/4.49  --soft_lemma_size                       3
% 31.77/4.49  --prop_impl_unit_size                   0
% 31.77/4.49  --prop_impl_unit                        []
% 31.77/4.49  --share_sel_clauses                     true
% 31.77/4.49  --reset_solvers                         false
% 31.77/4.49  --bc_imp_inh                            [conj_cone]
% 31.77/4.49  --conj_cone_tolerance                   3.
% 31.77/4.49  --extra_neg_conj                        none
% 31.77/4.49  --large_theory_mode                     true
% 31.77/4.49  --prolific_symb_bound                   200
% 31.77/4.49  --lt_threshold                          2000
% 31.77/4.49  --clause_weak_htbl                      true
% 31.77/4.49  --gc_record_bc_elim                     false
% 31.77/4.49  
% 31.77/4.49  ------ Preprocessing Options
% 31.77/4.49  
% 31.77/4.49  --preprocessing_flag                    true
% 31.77/4.49  --time_out_prep_mult                    0.1
% 31.77/4.49  --splitting_mode                        input
% 31.77/4.49  --splitting_grd                         true
% 31.77/4.49  --splitting_cvd                         false
% 31.77/4.49  --splitting_cvd_svl                     false
% 31.77/4.49  --splitting_nvd                         32
% 31.77/4.49  --sub_typing                            true
% 31.77/4.49  --prep_gs_sim                           true
% 31.77/4.49  --prep_unflatten                        true
% 31.77/4.49  --prep_res_sim                          true
% 31.77/4.49  --prep_upred                            true
% 31.77/4.49  --prep_sem_filter                       exhaustive
% 31.77/4.49  --prep_sem_filter_out                   false
% 31.77/4.49  --pred_elim                             true
% 31.77/4.49  --res_sim_input                         true
% 31.77/4.49  --eq_ax_congr_red                       true
% 31.77/4.49  --pure_diseq_elim                       true
% 31.77/4.49  --brand_transform                       false
% 31.77/4.49  --non_eq_to_eq                          false
% 31.77/4.49  --prep_def_merge                        true
% 31.77/4.49  --prep_def_merge_prop_impl              false
% 31.77/4.49  --prep_def_merge_mbd                    true
% 31.77/4.49  --prep_def_merge_tr_red                 false
% 31.77/4.49  --prep_def_merge_tr_cl                  false
% 31.77/4.49  --smt_preprocessing                     true
% 31.77/4.49  --smt_ac_axioms                         fast
% 31.77/4.49  --preprocessed_out                      false
% 31.77/4.49  --preprocessed_stats                    false
% 31.77/4.49  
% 31.77/4.49  ------ Abstraction refinement Options
% 31.77/4.49  
% 31.77/4.49  --abstr_ref                             []
% 31.77/4.49  --abstr_ref_prep                        false
% 31.77/4.49  --abstr_ref_until_sat                   false
% 31.77/4.49  --abstr_ref_sig_restrict                funpre
% 31.77/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.77/4.49  --abstr_ref_under                       []
% 31.77/4.49  
% 31.77/4.49  ------ SAT Options
% 31.77/4.49  
% 31.77/4.49  --sat_mode                              false
% 31.77/4.49  --sat_fm_restart_options                ""
% 31.77/4.49  --sat_gr_def                            false
% 31.77/4.49  --sat_epr_types                         true
% 31.77/4.49  --sat_non_cyclic_types                  false
% 31.77/4.49  --sat_finite_models                     false
% 31.77/4.49  --sat_fm_lemmas                         false
% 31.77/4.49  --sat_fm_prep                           false
% 31.77/4.49  --sat_fm_uc_incr                        true
% 31.77/4.49  --sat_out_model                         small
% 31.77/4.49  --sat_out_clauses                       false
% 31.77/4.49  
% 31.77/4.49  ------ QBF Options
% 31.77/4.49  
% 31.77/4.49  --qbf_mode                              false
% 31.77/4.49  --qbf_elim_univ                         false
% 31.77/4.49  --qbf_dom_inst                          none
% 31.77/4.49  --qbf_dom_pre_inst                      false
% 31.77/4.49  --qbf_sk_in                             false
% 31.77/4.49  --qbf_pred_elim                         true
% 31.77/4.49  --qbf_split                             512
% 31.77/4.49  
% 31.77/4.49  ------ BMC1 Options
% 31.77/4.49  
% 31.77/4.49  --bmc1_incremental                      false
% 31.77/4.49  --bmc1_axioms                           reachable_all
% 31.77/4.49  --bmc1_min_bound                        0
% 31.77/4.49  --bmc1_max_bound                        -1
% 31.77/4.49  --bmc1_max_bound_default                -1
% 31.77/4.49  --bmc1_symbol_reachability              true
% 31.77/4.49  --bmc1_property_lemmas                  false
% 31.77/4.49  --bmc1_k_induction                      false
% 31.77/4.49  --bmc1_non_equiv_states                 false
% 31.77/4.49  --bmc1_deadlock                         false
% 31.77/4.49  --bmc1_ucm                              false
% 31.77/4.49  --bmc1_add_unsat_core                   none
% 31.77/4.49  --bmc1_unsat_core_children              false
% 31.77/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.77/4.49  --bmc1_out_stat                         full
% 31.77/4.49  --bmc1_ground_init                      false
% 31.77/4.49  --bmc1_pre_inst_next_state              false
% 31.77/4.49  --bmc1_pre_inst_state                   false
% 31.77/4.49  --bmc1_pre_inst_reach_state             false
% 31.77/4.49  --bmc1_out_unsat_core                   false
% 31.77/4.49  --bmc1_aig_witness_out                  false
% 31.77/4.49  --bmc1_verbose                          false
% 31.77/4.49  --bmc1_dump_clauses_tptp                false
% 31.77/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.77/4.49  --bmc1_dump_file                        -
% 31.77/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.77/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.77/4.49  --bmc1_ucm_extend_mode                  1
% 31.77/4.49  --bmc1_ucm_init_mode                    2
% 31.77/4.49  --bmc1_ucm_cone_mode                    none
% 31.77/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.77/4.49  --bmc1_ucm_relax_model                  4
% 31.77/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.77/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.77/4.49  --bmc1_ucm_layered_model                none
% 31.77/4.49  --bmc1_ucm_max_lemma_size               10
% 31.77/4.49  
% 31.77/4.49  ------ AIG Options
% 31.77/4.49  
% 31.77/4.49  --aig_mode                              false
% 31.77/4.49  
% 31.77/4.49  ------ Instantiation Options
% 31.77/4.49  
% 31.77/4.49  --instantiation_flag                    true
% 31.77/4.49  --inst_sos_flag                         true
% 31.77/4.49  --inst_sos_phase                        true
% 31.77/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.77/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.77/4.49  --inst_lit_sel_side                     num_symb
% 31.77/4.49  --inst_solver_per_active                1400
% 31.77/4.49  --inst_solver_calls_frac                1.
% 31.77/4.49  --inst_passive_queue_type               priority_queues
% 31.77/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.77/4.49  --inst_passive_queues_freq              [25;2]
% 31.77/4.49  --inst_dismatching                      true
% 31.77/4.49  --inst_eager_unprocessed_to_passive     true
% 31.77/4.49  --inst_prop_sim_given                   true
% 31.77/4.49  --inst_prop_sim_new                     false
% 31.77/4.49  --inst_subs_new                         false
% 31.77/4.49  --inst_eq_res_simp                      false
% 31.77/4.49  --inst_subs_given                       false
% 31.77/4.49  --inst_orphan_elimination               true
% 31.77/4.49  --inst_learning_loop_flag               true
% 31.77/4.49  --inst_learning_start                   3000
% 31.77/4.49  --inst_learning_factor                  2
% 31.77/4.49  --inst_start_prop_sim_after_learn       3
% 31.77/4.49  --inst_sel_renew                        solver
% 31.77/4.49  --inst_lit_activity_flag                true
% 31.77/4.49  --inst_restr_to_given                   false
% 31.77/4.49  --inst_activity_threshold               500
% 31.77/4.49  --inst_out_proof                        true
% 31.77/4.49  
% 31.77/4.49  ------ Resolution Options
% 31.77/4.49  
% 31.77/4.49  --resolution_flag                       true
% 31.77/4.49  --res_lit_sel                           adaptive
% 31.77/4.49  --res_lit_sel_side                      none
% 31.77/4.49  --res_ordering                          kbo
% 31.77/4.49  --res_to_prop_solver                    active
% 31.77/4.49  --res_prop_simpl_new                    false
% 31.77/4.49  --res_prop_simpl_given                  true
% 31.77/4.49  --res_passive_queue_type                priority_queues
% 31.77/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.77/4.49  --res_passive_queues_freq               [15;5]
% 31.77/4.49  --res_forward_subs                      full
% 31.77/4.49  --res_backward_subs                     full
% 31.77/4.49  --res_forward_subs_resolution           true
% 31.77/4.49  --res_backward_subs_resolution          true
% 31.77/4.49  --res_orphan_elimination                true
% 31.77/4.49  --res_time_limit                        2.
% 31.77/4.49  --res_out_proof                         true
% 31.77/4.49  
% 31.77/4.49  ------ Superposition Options
% 31.77/4.49  
% 31.77/4.49  --superposition_flag                    true
% 31.77/4.49  --sup_passive_queue_type                priority_queues
% 31.77/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.77/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.77/4.49  --demod_completeness_check              fast
% 31.77/4.49  --demod_use_ground                      true
% 31.77/4.49  --sup_to_prop_solver                    passive
% 31.77/4.49  --sup_prop_simpl_new                    true
% 31.77/4.49  --sup_prop_simpl_given                  true
% 31.77/4.49  --sup_fun_splitting                     true
% 31.77/4.49  --sup_smt_interval                      50000
% 31.77/4.49  
% 31.77/4.49  ------ Superposition Simplification Setup
% 31.77/4.49  
% 31.77/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.77/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.77/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.77/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.77/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.77/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.77/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.77/4.49  --sup_immed_triv                        [TrivRules]
% 31.77/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.49  --sup_immed_bw_main                     []
% 31.77/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.77/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.77/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.49  --sup_input_bw                          []
% 31.77/4.49  
% 31.77/4.49  ------ Combination Options
% 31.77/4.49  
% 31.77/4.49  --comb_res_mult                         3
% 31.77/4.49  --comb_sup_mult                         2
% 31.77/4.49  --comb_inst_mult                        10
% 31.77/4.49  
% 31.77/4.49  ------ Debug Options
% 31.77/4.49  
% 31.77/4.49  --dbg_backtrace                         false
% 31.77/4.49  --dbg_dump_prop_clauses                 false
% 31.77/4.49  --dbg_dump_prop_clauses_file            -
% 31.77/4.49  --dbg_out_stat                          false
% 31.77/4.49  ------ Parsing...
% 31.77/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.77/4.49  
% 31.77/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.77/4.49  
% 31.77/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.77/4.49  
% 31.77/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.77/4.49  ------ Proving...
% 31.77/4.49  ------ Problem Properties 
% 31.77/4.49  
% 31.77/4.49  
% 31.77/4.49  clauses                                 13
% 31.77/4.49  conjectures                             3
% 31.77/4.49  EPR                                     0
% 31.77/4.49  Horn                                    13
% 31.77/4.49  unary                                   5
% 31.77/4.49  binary                                  5
% 31.77/4.49  lits                                    25
% 31.77/4.49  lits eq                                 3
% 31.77/4.49  fd_pure                                 0
% 31.77/4.49  fd_pseudo                               0
% 31.77/4.49  fd_cond                                 0
% 31.77/4.49  fd_pseudo_cond                          0
% 31.77/4.49  AC symbols                              0
% 31.77/4.49  
% 31.77/4.49  ------ Schedule dynamic 5 is on 
% 31.77/4.49  
% 31.77/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.77/4.49  
% 31.77/4.49  
% 31.77/4.49  ------ 
% 31.77/4.49  Current options:
% 31.77/4.49  ------ 
% 31.77/4.49  
% 31.77/4.49  ------ Input Options
% 31.77/4.49  
% 31.77/4.49  --out_options                           all
% 31.77/4.49  --tptp_safe_out                         true
% 31.77/4.49  --problem_path                          ""
% 31.77/4.49  --include_path                          ""
% 31.77/4.49  --clausifier                            res/vclausify_rel
% 31.77/4.49  --clausifier_options                    ""
% 31.77/4.49  --stdin                                 false
% 31.77/4.49  --stats_out                             all
% 31.77/4.49  
% 31.77/4.49  ------ General Options
% 31.77/4.49  
% 31.77/4.49  --fof                                   false
% 31.77/4.49  --time_out_real                         305.
% 31.77/4.49  --time_out_virtual                      -1.
% 31.77/4.49  --symbol_type_check                     false
% 31.77/4.49  --clausify_out                          false
% 31.77/4.49  --sig_cnt_out                           false
% 31.77/4.49  --trig_cnt_out                          false
% 31.77/4.49  --trig_cnt_out_tolerance                1.
% 31.77/4.49  --trig_cnt_out_sk_spl                   false
% 31.77/4.49  --abstr_cl_out                          false
% 31.77/4.49  
% 31.77/4.49  ------ Global Options
% 31.77/4.49  
% 31.77/4.49  --schedule                              default
% 31.77/4.49  --add_important_lit                     false
% 31.77/4.49  --prop_solver_per_cl                    1000
% 31.77/4.49  --min_unsat_core                        false
% 31.77/4.49  --soft_assumptions                      false
% 31.77/4.49  --soft_lemma_size                       3
% 31.77/4.49  --prop_impl_unit_size                   0
% 31.77/4.49  --prop_impl_unit                        []
% 31.77/4.49  --share_sel_clauses                     true
% 31.77/4.49  --reset_solvers                         false
% 31.77/4.49  --bc_imp_inh                            [conj_cone]
% 31.77/4.49  --conj_cone_tolerance                   3.
% 31.77/4.49  --extra_neg_conj                        none
% 31.77/4.49  --large_theory_mode                     true
% 31.77/4.49  --prolific_symb_bound                   200
% 31.77/4.49  --lt_threshold                          2000
% 31.77/4.49  --clause_weak_htbl                      true
% 31.77/4.49  --gc_record_bc_elim                     false
% 31.77/4.49  
% 31.77/4.49  ------ Preprocessing Options
% 31.77/4.49  
% 31.77/4.49  --preprocessing_flag                    true
% 31.77/4.49  --time_out_prep_mult                    0.1
% 31.77/4.49  --splitting_mode                        input
% 31.77/4.49  --splitting_grd                         true
% 31.77/4.49  --splitting_cvd                         false
% 31.77/4.49  --splitting_cvd_svl                     false
% 31.77/4.49  --splitting_nvd                         32
% 31.77/4.49  --sub_typing                            true
% 31.77/4.49  --prep_gs_sim                           true
% 31.77/4.49  --prep_unflatten                        true
% 31.77/4.49  --prep_res_sim                          true
% 31.77/4.49  --prep_upred                            true
% 31.77/4.49  --prep_sem_filter                       exhaustive
% 31.77/4.49  --prep_sem_filter_out                   false
% 31.77/4.49  --pred_elim                             true
% 31.77/4.49  --res_sim_input                         true
% 31.77/4.49  --eq_ax_congr_red                       true
% 31.77/4.49  --pure_diseq_elim                       true
% 31.77/4.49  --brand_transform                       false
% 31.77/4.49  --non_eq_to_eq                          false
% 31.77/4.49  --prep_def_merge                        true
% 31.77/4.49  --prep_def_merge_prop_impl              false
% 31.77/4.49  --prep_def_merge_mbd                    true
% 31.77/4.49  --prep_def_merge_tr_red                 false
% 31.77/4.49  --prep_def_merge_tr_cl                  false
% 31.77/4.49  --smt_preprocessing                     true
% 31.77/4.49  --smt_ac_axioms                         fast
% 31.77/4.49  --preprocessed_out                      false
% 31.77/4.49  --preprocessed_stats                    false
% 31.77/4.49  
% 31.77/4.49  ------ Abstraction refinement Options
% 31.77/4.49  
% 31.77/4.49  --abstr_ref                             []
% 31.77/4.49  --abstr_ref_prep                        false
% 31.77/4.49  --abstr_ref_until_sat                   false
% 31.77/4.49  --abstr_ref_sig_restrict                funpre
% 31.77/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.77/4.49  --abstr_ref_under                       []
% 31.77/4.49  
% 31.77/4.49  ------ SAT Options
% 31.77/4.49  
% 31.77/4.49  --sat_mode                              false
% 31.77/4.49  --sat_fm_restart_options                ""
% 31.77/4.49  --sat_gr_def                            false
% 31.77/4.49  --sat_epr_types                         true
% 31.77/4.49  --sat_non_cyclic_types                  false
% 31.77/4.49  --sat_finite_models                     false
% 31.77/4.49  --sat_fm_lemmas                         false
% 31.77/4.49  --sat_fm_prep                           false
% 31.77/4.49  --sat_fm_uc_incr                        true
% 31.77/4.49  --sat_out_model                         small
% 31.77/4.49  --sat_out_clauses                       false
% 31.77/4.49  
% 31.77/4.49  ------ QBF Options
% 31.77/4.49  
% 31.77/4.49  --qbf_mode                              false
% 31.77/4.49  --qbf_elim_univ                         false
% 31.77/4.49  --qbf_dom_inst                          none
% 31.77/4.49  --qbf_dom_pre_inst                      false
% 31.77/4.49  --qbf_sk_in                             false
% 31.77/4.49  --qbf_pred_elim                         true
% 31.77/4.49  --qbf_split                             512
% 31.77/4.49  
% 31.77/4.49  ------ BMC1 Options
% 31.77/4.49  
% 31.77/4.49  --bmc1_incremental                      false
% 31.77/4.49  --bmc1_axioms                           reachable_all
% 31.77/4.49  --bmc1_min_bound                        0
% 31.77/4.49  --bmc1_max_bound                        -1
% 31.77/4.49  --bmc1_max_bound_default                -1
% 31.77/4.49  --bmc1_symbol_reachability              true
% 31.77/4.49  --bmc1_property_lemmas                  false
% 31.77/4.49  --bmc1_k_induction                      false
% 31.77/4.49  --bmc1_non_equiv_states                 false
% 31.77/4.49  --bmc1_deadlock                         false
% 31.77/4.49  --bmc1_ucm                              false
% 31.77/4.49  --bmc1_add_unsat_core                   none
% 31.77/4.49  --bmc1_unsat_core_children              false
% 31.77/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.77/4.49  --bmc1_out_stat                         full
% 31.77/4.49  --bmc1_ground_init                      false
% 31.77/4.49  --bmc1_pre_inst_next_state              false
% 31.77/4.49  --bmc1_pre_inst_state                   false
% 31.77/4.49  --bmc1_pre_inst_reach_state             false
% 31.77/4.49  --bmc1_out_unsat_core                   false
% 31.77/4.49  --bmc1_aig_witness_out                  false
% 31.77/4.49  --bmc1_verbose                          false
% 31.77/4.49  --bmc1_dump_clauses_tptp                false
% 31.77/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.77/4.49  --bmc1_dump_file                        -
% 31.77/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.77/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.77/4.49  --bmc1_ucm_extend_mode                  1
% 31.77/4.49  --bmc1_ucm_init_mode                    2
% 31.77/4.49  --bmc1_ucm_cone_mode                    none
% 31.77/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.77/4.49  --bmc1_ucm_relax_model                  4
% 31.77/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.77/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.77/4.49  --bmc1_ucm_layered_model                none
% 31.77/4.49  --bmc1_ucm_max_lemma_size               10
% 31.77/4.49  
% 31.77/4.49  ------ AIG Options
% 31.77/4.49  
% 31.77/4.49  --aig_mode                              false
% 31.77/4.49  
% 31.77/4.49  ------ Instantiation Options
% 31.77/4.49  
% 31.77/4.49  --instantiation_flag                    true
% 31.77/4.49  --inst_sos_flag                         true
% 31.77/4.49  --inst_sos_phase                        true
% 31.77/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.77/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.77/4.49  --inst_lit_sel_side                     none
% 31.77/4.49  --inst_solver_per_active                1400
% 31.77/4.49  --inst_solver_calls_frac                1.
% 31.77/4.49  --inst_passive_queue_type               priority_queues
% 31.77/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.77/4.49  --inst_passive_queues_freq              [25;2]
% 31.77/4.49  --inst_dismatching                      true
% 31.77/4.49  --inst_eager_unprocessed_to_passive     true
% 31.77/4.49  --inst_prop_sim_given                   true
% 31.77/4.49  --inst_prop_sim_new                     false
% 31.77/4.49  --inst_subs_new                         false
% 31.77/4.49  --inst_eq_res_simp                      false
% 31.77/4.49  --inst_subs_given                       false
% 31.77/4.49  --inst_orphan_elimination               true
% 31.77/4.49  --inst_learning_loop_flag               true
% 31.77/4.49  --inst_learning_start                   3000
% 31.77/4.49  --inst_learning_factor                  2
% 31.77/4.49  --inst_start_prop_sim_after_learn       3
% 31.77/4.49  --inst_sel_renew                        solver
% 31.77/4.49  --inst_lit_activity_flag                true
% 31.77/4.49  --inst_restr_to_given                   false
% 31.77/4.49  --inst_activity_threshold               500
% 31.77/4.49  --inst_out_proof                        true
% 31.77/4.49  
% 31.77/4.49  ------ Resolution Options
% 31.77/4.49  
% 31.77/4.49  --resolution_flag                       false
% 31.77/4.49  --res_lit_sel                           adaptive
% 31.77/4.49  --res_lit_sel_side                      none
% 31.77/4.49  --res_ordering                          kbo
% 31.77/4.49  --res_to_prop_solver                    active
% 31.77/4.49  --res_prop_simpl_new                    false
% 31.77/4.49  --res_prop_simpl_given                  true
% 31.77/4.49  --res_passive_queue_type                priority_queues
% 31.77/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.77/4.49  --res_passive_queues_freq               [15;5]
% 31.77/4.49  --res_forward_subs                      full
% 31.77/4.49  --res_backward_subs                     full
% 31.77/4.49  --res_forward_subs_resolution           true
% 31.77/4.49  --res_backward_subs_resolution          true
% 31.77/4.49  --res_orphan_elimination                true
% 31.77/4.49  --res_time_limit                        2.
% 31.77/4.49  --res_out_proof                         true
% 31.77/4.49  
% 31.77/4.49  ------ Superposition Options
% 31.77/4.49  
% 31.77/4.49  --superposition_flag                    true
% 31.77/4.49  --sup_passive_queue_type                priority_queues
% 31.77/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.77/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.77/4.49  --demod_completeness_check              fast
% 31.77/4.49  --demod_use_ground                      true
% 31.77/4.49  --sup_to_prop_solver                    passive
% 31.77/4.49  --sup_prop_simpl_new                    true
% 31.77/4.49  --sup_prop_simpl_given                  true
% 31.77/4.49  --sup_fun_splitting                     true
% 31.77/4.49  --sup_smt_interval                      50000
% 31.77/4.49  
% 31.77/4.49  ------ Superposition Simplification Setup
% 31.77/4.49  
% 31.77/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.77/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.77/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.77/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.77/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.77/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.77/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.77/4.49  --sup_immed_triv                        [TrivRules]
% 31.77/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.49  --sup_immed_bw_main                     []
% 31.77/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.77/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.77/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.77/4.49  --sup_input_bw                          []
% 31.77/4.49  
% 31.77/4.49  ------ Combination Options
% 31.77/4.49  
% 31.77/4.49  --comb_res_mult                         3
% 31.77/4.49  --comb_sup_mult                         2
% 31.77/4.49  --comb_inst_mult                        10
% 31.77/4.49  
% 31.77/4.49  ------ Debug Options
% 31.77/4.49  
% 31.77/4.49  --dbg_backtrace                         false
% 31.77/4.49  --dbg_dump_prop_clauses                 false
% 31.77/4.49  --dbg_dump_prop_clauses_file            -
% 31.77/4.49  --dbg_out_stat                          false
% 31.77/4.49  
% 31.77/4.49  
% 31.77/4.49  
% 31.77/4.49  
% 31.77/4.49  ------ Proving...
% 31.77/4.49  
% 31.77/4.49  
% 31.77/4.49  % SZS status Theorem for theBenchmark.p
% 31.77/4.49  
% 31.77/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.77/4.49  
% 31.77/4.49  fof(f10,conjecture,(
% 31.77/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f11,negated_conjecture,(
% 31.77/4.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 31.77/4.49    inference(negated_conjecture,[],[f10])).
% 31.77/4.49  
% 31.77/4.49  fof(f21,plain,(
% 31.77/4.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 31.77/4.49    inference(ennf_transformation,[],[f11])).
% 31.77/4.49  
% 31.77/4.49  fof(f25,plain,(
% 31.77/4.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.77/4.49    introduced(choice_axiom,[])).
% 31.77/4.49  
% 31.77/4.49  fof(f24,plain,(
% 31.77/4.49    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.77/4.49    introduced(choice_axiom,[])).
% 31.77/4.49  
% 31.77/4.49  fof(f23,plain,(
% 31.77/4.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 31.77/4.49    introduced(choice_axiom,[])).
% 31.77/4.49  
% 31.77/4.49  fof(f26,plain,(
% 31.77/4.49    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 31.77/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).
% 31.77/4.49  
% 31.77/4.49  fof(f38,plain,(
% 31.77/4.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.77/4.49    inference(cnf_transformation,[],[f26])).
% 31.77/4.49  
% 31.77/4.49  fof(f7,axiom,(
% 31.77/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f22,plain,(
% 31.77/4.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.77/4.49    inference(nnf_transformation,[],[f7])).
% 31.77/4.49  
% 31.77/4.49  fof(f33,plain,(
% 31.77/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.77/4.49    inference(cnf_transformation,[],[f22])).
% 31.77/4.49  
% 31.77/4.49  fof(f39,plain,(
% 31.77/4.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.77/4.49    inference(cnf_transformation,[],[f26])).
% 31.77/4.49  
% 31.77/4.49  fof(f5,axiom,(
% 31.77/4.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f14,plain,(
% 31.77/4.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 31.77/4.49    inference(ennf_transformation,[],[f5])).
% 31.77/4.49  
% 31.77/4.49  fof(f15,plain,(
% 31.77/4.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 31.77/4.49    inference(flattening,[],[f14])).
% 31.77/4.49  
% 31.77/4.49  fof(f31,plain,(
% 31.77/4.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 31.77/4.49    inference(cnf_transformation,[],[f15])).
% 31.77/4.49  
% 31.77/4.49  fof(f3,axiom,(
% 31.77/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f13,plain,(
% 31.77/4.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 31.77/4.49    inference(ennf_transformation,[],[f3])).
% 31.77/4.49  
% 31.77/4.49  fof(f29,plain,(
% 31.77/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 31.77/4.49    inference(cnf_transformation,[],[f13])).
% 31.77/4.49  
% 31.77/4.49  fof(f1,axiom,(
% 31.77/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f27,plain,(
% 31.77/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 31.77/4.49    inference(cnf_transformation,[],[f1])).
% 31.77/4.49  
% 31.77/4.49  fof(f4,axiom,(
% 31.77/4.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f30,plain,(
% 31.77/4.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.77/4.49    inference(cnf_transformation,[],[f4])).
% 31.77/4.49  
% 31.77/4.49  fof(f2,axiom,(
% 31.77/4.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f12,plain,(
% 31.77/4.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 31.77/4.49    inference(ennf_transformation,[],[f2])).
% 31.77/4.49  
% 31.77/4.49  fof(f28,plain,(
% 31.77/4.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 31.77/4.49    inference(cnf_transformation,[],[f12])).
% 31.77/4.49  
% 31.77/4.49  fof(f9,axiom,(
% 31.77/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f19,plain,(
% 31.77/4.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.77/4.49    inference(ennf_transformation,[],[f9])).
% 31.77/4.49  
% 31.77/4.49  fof(f20,plain,(
% 31.77/4.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.77/4.49    inference(flattening,[],[f19])).
% 31.77/4.49  
% 31.77/4.49  fof(f36,plain,(
% 31.77/4.49    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.77/4.49    inference(cnf_transformation,[],[f20])).
% 31.77/4.49  
% 31.77/4.49  fof(f37,plain,(
% 31.77/4.49    l1_pre_topc(sK0)),
% 31.77/4.49    inference(cnf_transformation,[],[f26])).
% 31.77/4.49  
% 31.77/4.49  fof(f34,plain,(
% 31.77/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.77/4.49    inference(cnf_transformation,[],[f22])).
% 31.77/4.49  
% 31.77/4.49  fof(f6,axiom,(
% 31.77/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f16,plain,(
% 31.77/4.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.77/4.49    inference(ennf_transformation,[],[f6])).
% 31.77/4.49  
% 31.77/4.49  fof(f17,plain,(
% 31.77/4.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.77/4.49    inference(flattening,[],[f16])).
% 31.77/4.49  
% 31.77/4.49  fof(f32,plain,(
% 31.77/4.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.77/4.49    inference(cnf_transformation,[],[f17])).
% 31.77/4.49  
% 31.77/4.49  fof(f8,axiom,(
% 31.77/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 31.77/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.77/4.49  
% 31.77/4.49  fof(f18,plain,(
% 31.77/4.49    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.77/4.49    inference(ennf_transformation,[],[f8])).
% 31.77/4.49  
% 31.77/4.49  fof(f35,plain,(
% 31.77/4.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.77/4.49    inference(cnf_transformation,[],[f18])).
% 31.77/4.49  
% 31.77/4.49  fof(f40,plain,(
% 31.77/4.49    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 31.77/4.49    inference(cnf_transformation,[],[f26])).
% 31.77/4.49  
% 31.77/4.49  cnf(c_335,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.77/4.49      theory(equality) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_97627,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,X1)
% 31.77/4.49      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.77/4.49      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 31.77/4.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_335]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_97965,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
% 31.77/4.49      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.77/4.49      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 31.77/4.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_97627]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_98453,plain,
% 31.77/4.49      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.77/4.49      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1))
% 31.77/4.49      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.77/4.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,X1) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_97965]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_137113,plain,
% 31.77/4.49      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.77/4.49      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.77/4.49      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.77/4.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_98453]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_12,negated_conjecture,
% 31.77/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.77/4.49      inference(cnf_transformation,[],[f38]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_628,plain,
% 31.77/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_7,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.77/4.49      inference(cnf_transformation,[],[f33]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_631,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.77/4.49      | r1_tarski(X0,X1) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1306,plain,
% 31.77/4.49      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_628,c_631]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_11,negated_conjecture,
% 31.77/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.77/4.49      inference(cnf_transformation,[],[f39]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_629,plain,
% 31.77/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1305,plain,
% 31.77/4.49      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_629,c_631]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_4,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,X1)
% 31.77/4.49      | ~ r1_tarski(X2,X1)
% 31.77/4.49      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 31.77/4.49      inference(cnf_transformation,[],[f31]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_633,plain,
% 31.77/4.49      ( r1_tarski(X0,X1) != iProver_top
% 31.77/4.49      | r1_tarski(X2,X1) != iProver_top
% 31.77/4.49      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_2,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 31.77/4.49      inference(cnf_transformation,[],[f29]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_635,plain,
% 31.77/4.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_2256,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = X2
% 31.77/4.49      | r1_tarski(X0,X2) != iProver_top
% 31.77/4.49      | r1_tarski(X1,X2) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_633,c_635]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_20149,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(sK2,X0),u1_struct_0(sK0)) = u1_struct_0(sK0)
% 31.77/4.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_1305,c_2256]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_22970,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(sK2,sK1),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_1306,c_20149]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_0,plain,
% 31.77/4.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 31.77/4.49      inference(cnf_transformation,[],[f27]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_3,plain,
% 31.77/4.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 31.77/4.49      inference(cnf_transformation,[],[f30]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_634,plain,
% 31.77/4.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1207,plain,
% 31.77/4.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_634,c_635]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_4589,plain,
% 31.77/4.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_0,c_1207]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1,plain,
% 31.77/4.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 31.77/4.49      inference(cnf_transformation,[],[f28]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_636,plain,
% 31.77/4.49      ( r1_tarski(X0,X1) = iProver_top
% 31.77/4.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1772,plain,
% 31.77/4.49      ( r1_tarski(X0,X1) = iProver_top
% 31.77/4.49      | r1_tarski(k2_xboole_0(X2,X0),X1) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_0,c_636]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1800,plain,
% 31.77/4.49      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_634,c_1772]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_7348,plain,
% 31.77/4.49      ( r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_4589,c_1800]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_23060,plain,
% 31.77/4.49      ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_22970,c_7348]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_9,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.77/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.77/4.49      | ~ r1_tarski(X0,X2)
% 31.77/4.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 31.77/4.49      | ~ l1_pre_topc(X1) ),
% 31.77/4.49      inference(cnf_transformation,[],[f36]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_13,negated_conjecture,
% 31.77/4.49      ( l1_pre_topc(sK0) ),
% 31.77/4.49      inference(cnf_transformation,[],[f37]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_180,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.77/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.77/4.49      | ~ r1_tarski(X0,X2)
% 31.77/4.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 31.77/4.49      | sK0 != X1 ),
% 31.77/4.49      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_181,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.77/4.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.77/4.49      | ~ r1_tarski(X1,X0)
% 31.77/4.49      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 31.77/4.49      inference(unflattening,[status(thm)],[c_180]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_627,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | r1_tarski(X1,X0) != iProver_top
% 31.77/4.49      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_181]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_6,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.77/4.49      inference(cnf_transformation,[],[f34]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_632,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.77/4.49      | r1_tarski(X0,X1) != iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_20151,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,X0),X1),k1_tops_1(sK0,X2)) = k1_tops_1(sK0,X2)
% 31.77/4.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | r1_tarski(X0,X2) != iProver_top
% 31.77/4.49      | r1_tarski(X1,k1_tops_1(sK0,X2)) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_627,c_2256]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_27999,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 31.77/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
% 31.77/4.49      | r1_tarski(sK1,X1) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_628,c_20151]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_28475,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 31.77/4.49      | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
% 31.77/4.49      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 31.77/4.49      | r1_tarski(sK1,X1) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_632,c_27999]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_29611,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 31.77/4.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | r1_tarski(X0,X1) != iProver_top
% 31.77/4.49      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 31.77/4.49      | r1_tarski(sK1,X1) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_627,c_28475]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_32858,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 31.77/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 31.77/4.49      | r1_tarski(sK2,X0) != iProver_top
% 31.77/4.49      | r1_tarski(sK1,X0) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_629,c_29611]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_673,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.77/4.49      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_6]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_674,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 31.77/4.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_33015,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 31.77/4.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 31.77/4.49      | r1_tarski(sK2,X0) != iProver_top
% 31.77/4.49      | r1_tarski(sK1,X0) != iProver_top ),
% 31.77/4.49      inference(global_propositional_subsumption,
% 31.77/4.49                [status(thm)],
% 31.77/4.49                [c_32858,c_674]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_91382,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.77/4.49      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top
% 31.77/4.49      | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_23060,c_33015]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_333,plain,( X0 = X0 ),theory(equality) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1282,plain,
% 31.77/4.49      ( sK2 = sK2 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_333]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_6920,plain,
% 31.77/4.49      ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_3]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_6921,plain,
% 31.77/4.49      ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_6920]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_6923,plain,
% 31.77/4.49      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_3]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_6924,plain,
% 31.77/4.49      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_6923]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_40120,plain,
% 31.77/4.49      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_0]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_4869,plain,
% 31.77/4.49      ( r1_tarski(X0,X1)
% 31.77/4.49      | ~ r1_tarski(X2,k2_xboole_0(X2,X3))
% 31.77/4.49      | X0 != X2
% 31.77/4.49      | X1 != k2_xboole_0(X2,X3) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_335]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_10561,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,k2_xboole_0(X0,X1))
% 31.77/4.49      | r1_tarski(X2,k2_xboole_0(X1,X0))
% 31.77/4.49      | X2 != X0
% 31.77/4.49      | k2_xboole_0(X1,X0) != k2_xboole_0(X0,X1) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_4869]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_18102,plain,
% 31.77/4.49      ( r1_tarski(X0,k2_xboole_0(sK1,sK2))
% 31.77/4.49      | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1))
% 31.77/4.49      | X0 != sK2
% 31.77/4.49      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_10561]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_73128,plain,
% 31.77/4.49      ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1))
% 31.77/4.49      | r1_tarski(sK2,k2_xboole_0(sK1,sK2))
% 31.77/4.49      | k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1)
% 31.77/4.49      | sK2 != sK2 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_18102]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_73129,plain,
% 31.77/4.49      ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1)
% 31.77/4.49      | sK2 != sK2
% 31.77/4.49      | r1_tarski(sK2,k2_xboole_0(sK2,sK1)) != iProver_top
% 31.77/4.49      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_73128]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_91702,plain,
% 31.77/4.49      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 31.77/4.49      inference(global_propositional_subsumption,
% 31.77/4.49                [status(thm)],
% 31.77/4.49                [c_91382,c_1282,c_6921,c_6924,c_40120,c_73129]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_91773,plain,
% 31.77/4.49      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_91702,c_634]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_92023,plain,
% 31.77/4.49      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
% 31.77/4.49      inference(predicate_to_equality_rev,[status(thm)],[c_91773]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_737,plain,
% 31.77/4.49      ( r1_tarski(X0,u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK0)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_20943,plain,
% 31.77/4.49      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),sK1),u1_struct_0(sK0)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_737]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_752,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,X1)
% 31.77/4.49      | r1_tarski(X2,u1_struct_0(sK0))
% 31.77/4.49      | X2 != X0
% 31.77/4.49      | u1_struct_0(sK0) != X1 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_335]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1163,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,u1_struct_0(sK0))
% 31.77/4.49      | r1_tarski(X1,u1_struct_0(sK0))
% 31.77/4.49      | X1 != X0
% 31.77/4.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_752]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1566,plain,
% 31.77/4.49      ( r1_tarski(X0,u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 31.77/4.49      | X0 != sK1
% 31.77/4.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1163]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1848,plain,
% 31.77/4.49      ( r1_tarski(k2_xboole_0(X0,sK1),u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 31.77/4.49      | k2_xboole_0(X0,sK1) != sK1
% 31.77/4.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1566]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_7033,plain,
% 31.77/4.49      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),sK1),u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 31.77/4.49      | k2_xboole_0(k1_tops_1(sK0,sK1),sK1) != sK1
% 31.77/4.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1848]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_4027,plain,
% 31.77/4.49      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_737]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1561,plain,
% 31.77/4.49      ( r1_tarski(X0,u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.77/4.49      | X0 != sK2
% 31.77/4.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1163]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1841,plain,
% 31.77/4.49      ( r1_tarski(k2_xboole_0(X0,sK2),u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.77/4.49      | k2_xboole_0(X0,sK2) != sK2
% 31.77/4.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1561]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_3033,plain,
% 31.77/4.49      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK2),sK2),u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.77/4.49      | k2_xboole_0(k1_tops_1(sK0,sK2),sK2) != sK2
% 31.77/4.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1841]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_339,plain,
% 31.77/4.49      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 31.77/4.49      theory(equality) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1149,plain,
% 31.77/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 31.77/4.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 31.77/4.49      | sK0 != X1 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_339]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1555,plain,
% 31.77/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.77/4.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
% 31.77/4.49      | sK0 != X0 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1149]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1556,plain,
% 31.77/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.77/4.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.77/4.49      | sK0 != sK0 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_1555]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_5,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.77/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.77/4.49      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.77/4.49      inference(cnf_transformation,[],[f32]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_104,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.77/4.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_105,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.77/4.49      inference(renaming,[status(thm)],[c_104]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_128,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.77/4.49      | ~ r1_tarski(X2,X1)
% 31.77/4.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.77/4.49      inference(bin_hyper_res,[status(thm)],[c_5,c_105]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_261,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.77/4.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_262,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.77/4.49      inference(renaming,[status(thm)],[c_261]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_284,plain,
% 31.77/4.49      ( ~ r1_tarski(X0,X1)
% 31.77/4.49      | ~ r1_tarski(X2,X1)
% 31.77/4.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.77/4.49      inference(bin_hyper_res,[status(thm)],[c_128,c_262]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_625,plain,
% 31.77/4.49      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 31.77/4.49      | r1_tarski(X1,X0) != iProver_top
% 31.77/4.49      | r1_tarski(X2,X0) != iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1311,plain,
% 31.77/4.49      ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
% 31.77/4.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_1305,c_625]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1531,plain,
% 31.77/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_1306,c_1311]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_8,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.77/4.49      | r1_tarski(k1_tops_1(X1,X0),X0)
% 31.77/4.49      | ~ l1_pre_topc(X1) ),
% 31.77/4.49      inference(cnf_transformation,[],[f35]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_198,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.77/4.49      | r1_tarski(k1_tops_1(X1,X0),X0)
% 31.77/4.49      | sK0 != X1 ),
% 31.77/4.49      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_199,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.77/4.49      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 31.77/4.49      inference(unflattening,[status(thm)],[c_198]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_626,plain,
% 31.77/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.77/4.49      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 31.77/4.49      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_889,plain,
% 31.77/4.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_628,c_626]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1210,plain,
% 31.77/4.49      ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_889,c_635]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_888,plain,
% 31.77/4.49      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_629,c_626]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1209,plain,
% 31.77/4.49      ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
% 31.77/4.49      inference(superposition,[status(thm)],[c_888,c_635]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_1111,plain,
% 31.77/4.49      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 31.77/4.49      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 31.77/4.49      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_284]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_738,plain,
% 31.77/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.77/4.49      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_7]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_911,plain,
% 31.77/4.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.77/4.49      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_738]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_908,plain,
% 31.77/4.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.77/4.49      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_738]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_348,plain,
% 31.77/4.49      ( sK0 = sK0 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_333]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_340,plain,
% 31.77/4.49      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 31.77/4.49      theory(equality) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_346,plain,
% 31.77/4.49      ( u1_struct_0(sK0) = u1_struct_0(sK0) | sK0 != sK0 ),
% 31.77/4.49      inference(instantiation,[status(thm)],[c_340]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(c_10,negated_conjecture,
% 31.77/4.49      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.77/4.49      inference(cnf_transformation,[],[f40]) ).
% 31.77/4.49  
% 31.77/4.49  cnf(contradiction,plain,
% 31.77/4.49      ( $false ),
% 31.77/4.49      inference(minisat,
% 31.77/4.49                [status(thm)],
% 31.77/4.49                [c_137113,c_92023,c_20943,c_7033,c_4027,c_3033,c_1556,
% 31.77/4.49                 c_1531,c_1210,c_1209,c_1111,c_911,c_908,c_348,c_346,
% 31.77/4.49                 c_10,c_11,c_12]) ).
% 31.77/4.49  
% 31.77/4.49  
% 31.77/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.77/4.49  
% 31.77/4.49  ------                               Statistics
% 31.77/4.49  
% 31.77/4.49  ------ General
% 31.77/4.49  
% 31.77/4.49  abstr_ref_over_cycles:                  0
% 31.77/4.49  abstr_ref_under_cycles:                 0
% 31.77/4.49  gc_basic_clause_elim:                   0
% 31.77/4.49  forced_gc_time:                         0
% 31.77/4.49  parsing_time:                           0.006
% 31.77/4.49  unif_index_cands_time:                  0.
% 31.77/4.49  unif_index_add_time:                    0.
% 31.77/4.49  orderings_time:                         0.
% 31.77/4.49  out_proof_time:                         0.019
% 31.77/4.49  total_time:                             3.7
% 31.77/4.49  num_of_symbols:                         42
% 31.77/4.49  num_of_terms:                           130891
% 31.77/4.49  
% 31.77/4.49  ------ Preprocessing
% 31.77/4.49  
% 31.77/4.49  num_of_splits:                          0
% 31.77/4.49  num_of_split_atoms:                     0
% 31.77/4.49  num_of_reused_defs:                     0
% 31.77/4.49  num_eq_ax_congr_red:                    6
% 31.77/4.49  num_of_sem_filtered_clauses:            1
% 31.77/4.49  num_of_subtypes:                        0
% 31.77/4.49  monotx_restored_types:                  0
% 31.77/4.49  sat_num_of_epr_types:                   0
% 31.77/4.49  sat_num_of_non_cyclic_types:            0
% 31.77/4.49  sat_guarded_non_collapsed_types:        0
% 31.77/4.49  num_pure_diseq_elim:                    0
% 31.77/4.49  simp_replaced_by:                       0
% 31.77/4.49  res_preprocessed:                       70
% 31.77/4.49  prep_upred:                             0
% 31.77/4.49  prep_unflattend:                        2
% 31.77/4.49  smt_new_axioms:                         0
% 31.77/4.49  pred_elim_cands:                        2
% 31.77/4.49  pred_elim:                              1
% 31.77/4.49  pred_elim_cl:                           1
% 31.77/4.49  pred_elim_cycles:                       3
% 31.77/4.49  merged_defs:                            8
% 31.77/4.49  merged_defs_ncl:                        0
% 31.77/4.49  bin_hyper_res:                          10
% 31.77/4.49  prep_cycles:                            4
% 31.77/4.49  pred_elim_time:                         0.001
% 31.77/4.49  splitting_time:                         0.
% 31.77/4.49  sem_filter_time:                        0.
% 31.77/4.49  monotx_time:                            0.
% 31.77/4.49  subtype_inf_time:                       0.
% 31.77/4.49  
% 31.77/4.49  ------ Problem properties
% 31.77/4.49  
% 31.77/4.49  clauses:                                13
% 31.77/4.49  conjectures:                            3
% 31.77/4.49  epr:                                    0
% 31.77/4.49  horn:                                   13
% 31.77/4.49  ground:                                 3
% 31.77/4.49  unary:                                  5
% 31.77/4.49  binary:                                 5
% 31.77/4.49  lits:                                   25
% 31.77/4.49  lits_eq:                                3
% 31.77/4.49  fd_pure:                                0
% 31.77/4.49  fd_pseudo:                              0
% 31.77/4.49  fd_cond:                                0
% 31.77/4.49  fd_pseudo_cond:                         0
% 31.77/4.49  ac_symbols:                             0
% 31.77/4.49  
% 31.77/4.49  ------ Propositional Solver
% 31.77/4.49  
% 31.77/4.49  prop_solver_calls:                      51
% 31.77/4.49  prop_fast_solver_calls:                 3310
% 31.77/4.49  smt_solver_calls:                       0
% 31.77/4.49  smt_fast_solver_calls:                  0
% 31.77/4.49  prop_num_of_clauses:                    40947
% 31.77/4.49  prop_preprocess_simplified:             55672
% 31.77/4.49  prop_fo_subsumed:                       231
% 31.77/4.49  prop_solver_time:                       0.
% 31.77/4.49  smt_solver_time:                        0.
% 31.77/4.49  smt_fast_solver_time:                   0.
% 31.77/4.49  prop_fast_solver_time:                  0.
% 31.77/4.49  prop_unsat_core_time:                   0.005
% 31.77/4.49  
% 31.77/4.49  ------ QBF
% 31.77/4.49  
% 31.77/4.49  qbf_q_res:                              0
% 31.77/4.49  qbf_num_tautologies:                    0
% 31.77/4.49  qbf_prep_cycles:                        0
% 31.77/4.49  
% 31.77/4.49  ------ BMC1
% 31.77/4.49  
% 31.77/4.49  bmc1_current_bound:                     -1
% 31.77/4.49  bmc1_last_solved_bound:                 -1
% 31.77/4.49  bmc1_unsat_core_size:                   -1
% 31.77/4.49  bmc1_unsat_core_parents_size:           -1
% 31.77/4.49  bmc1_merge_next_fun:                    0
% 31.77/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.77/4.49  
% 31.77/4.49  ------ Instantiation
% 31.77/4.49  
% 31.77/4.49  inst_num_of_clauses:                    1841
% 31.77/4.49  inst_num_in_passive:                    821
% 31.77/4.49  inst_num_in_active:                     3737
% 31.77/4.49  inst_num_in_unprocessed:                9
% 31.77/4.49  inst_num_of_loops:                      4063
% 31.77/4.49  inst_num_of_learning_restarts:          1
% 31.77/4.49  inst_num_moves_active_passive:          318
% 31.77/4.49  inst_lit_activity:                      0
% 31.77/4.49  inst_lit_activity_moves:                6
% 31.77/4.49  inst_num_tautologies:                   0
% 31.77/4.49  inst_num_prop_implied:                  0
% 31.77/4.49  inst_num_existing_simplified:           0
% 31.77/4.49  inst_num_eq_res_simplified:             0
% 31.77/4.49  inst_num_child_elim:                    0
% 31.77/4.49  inst_num_of_dismatching_blockings:      21891
% 31.77/4.49  inst_num_of_non_proper_insts:           15419
% 31.77/4.49  inst_num_of_duplicates:                 0
% 31.77/4.49  inst_inst_num_from_inst_to_res:         0
% 31.77/4.49  inst_dismatching_checking_time:         0.
% 31.77/4.49  
% 31.77/4.49  ------ Resolution
% 31.77/4.49  
% 31.77/4.49  res_num_of_clauses:                     21
% 31.77/4.49  res_num_in_passive:                     21
% 31.77/4.49  res_num_in_active:                      0
% 31.77/4.49  res_num_of_loops:                       74
% 31.77/4.49  res_forward_subset_subsumed:            226
% 31.77/4.49  res_backward_subset_subsumed:           8
% 31.77/4.49  res_forward_subsumed:                   0
% 31.77/4.49  res_backward_subsumed:                  0
% 31.77/4.49  res_forward_subsumption_resolution:     0
% 31.77/4.49  res_backward_subsumption_resolution:    0
% 31.77/4.49  res_clause_to_clause_subsumption:       221830
% 31.77/4.49  res_orphan_elimination:                 0
% 31.77/4.49  res_tautology_del:                      285
% 31.77/4.49  res_num_eq_res_simplified:              0
% 31.77/4.49  res_num_sel_changes:                    0
% 31.77/4.49  res_moves_from_active_to_pass:          0
% 31.77/4.49  
% 31.77/4.49  ------ Superposition
% 31.77/4.49  
% 31.77/4.49  sup_time_total:                         0.
% 31.77/4.49  sup_time_generating:                    0.
% 31.77/4.49  sup_time_sim_full:                      0.
% 31.77/4.49  sup_time_sim_immed:                     0.
% 31.77/4.49  
% 31.77/4.49  sup_num_of_clauses:                     7206
% 31.77/4.49  sup_num_in_active:                      756
% 31.77/4.49  sup_num_in_passive:                     6450
% 31.77/4.49  sup_num_of_loops:                       812
% 31.77/4.49  sup_fw_superposition:                   24256
% 31.77/4.49  sup_bw_superposition:                   16062
% 31.77/4.49  sup_immediate_simplified:               14306
% 31.77/4.49  sup_given_eliminated:                   0
% 31.77/4.49  comparisons_done:                       0
% 31.77/4.49  comparisons_avoided:                    0
% 31.77/4.49  
% 31.77/4.49  ------ Simplifications
% 31.77/4.49  
% 31.77/4.49  
% 31.77/4.49  sim_fw_subset_subsumed:                 128
% 31.77/4.49  sim_bw_subset_subsumed:                 79
% 31.77/4.49  sim_fw_subsumed:                        3186
% 31.77/4.49  sim_bw_subsumed:                        82
% 31.77/4.49  sim_fw_subsumption_res:                 0
% 31.77/4.49  sim_bw_subsumption_res:                 0
% 31.77/4.49  sim_tautology_del:                      175
% 31.77/4.49  sim_eq_tautology_del:                   2329
% 31.77/4.49  sim_eq_res_simp:                        0
% 31.77/4.49  sim_fw_demodulated:                     6224
% 31.77/4.49  sim_bw_demodulated:                     77
% 31.77/4.49  sim_light_normalised:                   6310
% 31.77/4.49  sim_joinable_taut:                      0
% 31.77/4.49  sim_joinable_simp:                      0
% 31.77/4.49  sim_ac_normalised:                      0
% 31.77/4.49  sim_smt_subsumption:                    0
% 31.77/4.49  
%------------------------------------------------------------------------------
