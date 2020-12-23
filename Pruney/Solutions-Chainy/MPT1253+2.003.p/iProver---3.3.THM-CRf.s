%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:07 EST 2020

% Result     : Theorem 31.97s
% Output     : CNFRefutation 31.97s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 953 expanded)
%              Number of clauses        :   81 ( 350 expanded)
%              Number of leaves         :   17 ( 219 expanded)
%              Depth                    :   23
%              Number of atoms          :  302 (2837 expanded)
%              Number of equality atoms :  105 ( 406 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),sK1)
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f50,f49])).

fof(f83,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f85,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1146,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_1141,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_1452,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1146,c_1141])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1140,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_1546,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1140])).

cnf(c_34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1219,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_1220,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1219])).

cnf(c_2116,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1546,c_34,c_1220])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3162,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2116,c_1148])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1153,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20546,plain,
    ( k3_xboole_0(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3162,c_1153])).

cnf(c_16,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1949,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_16,c_22])).

cnf(c_4174,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1949,c_22])).

cnf(c_54554,plain,
    ( k3_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_20546,c_4174])).

cnf(c_3160,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1148])).

cnf(c_8,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1155,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_20,c_212])).

cnf(c_507,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_508,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_507])).

cnf(c_550,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_259,c_508])).

cnf(c_1139,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_3312,plain,
    ( k4_subset_1(X0,X1,k3_xboole_0(X0,X2)) = k2_xboole_0(X1,k3_xboole_0(X0,X2))
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1139])).

cnf(c_50093,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(u1_struct_0(sK0),X0)) = k2_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),X0)) ),
    inference(superposition,[status(thm)],[c_3160,c_3312])).

cnf(c_56035,plain,
    ( k2_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_54554,c_50093])).

cnf(c_56036,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_56035,c_54554])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_1142,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_1549,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1146,c_1142])).

cnf(c_56037,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_56036,c_1549])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1151,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3174,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1151])).

cnf(c_56177,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_56037,c_3174])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1156,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6161,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1151,c_1156])).

cnf(c_56163,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_56037,c_6161])).

cnf(c_56188,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_56163,c_56037])).

cnf(c_26,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_pre_topc(sK0,X0),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_359,plain,
    ( r1_tarski(k2_pre_topc(sK0,X0),sK1)
    | ~ r1_tarski(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_32,c_31])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_pre_topc(sK0,X0),sK1) ),
    inference(renaming,[status(thm)],[c_359])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_1629,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1143])).

cnf(c_1294,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_1295,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1404,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1405,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_1952,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_34,c_1295,c_1405])).

cnf(c_6165,plain,
    ( k2_xboole_0(k2_pre_topc(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1952,c_1156])).

cnf(c_6783,plain,
    ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_6165,c_1])).

cnf(c_56189,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_56188,c_6783])).

cnf(c_56391,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_56177,c_56189])).

cnf(c_29,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56391,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.97/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.97/4.49  
% 31.97/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.97/4.49  
% 31.97/4.49  ------  iProver source info
% 31.97/4.49  
% 31.97/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.97/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.97/4.49  git: non_committed_changes: false
% 31.97/4.49  git: last_make_outside_of_git: false
% 31.97/4.49  
% 31.97/4.49  ------ 
% 31.97/4.49  
% 31.97/4.49  ------ Input Options
% 31.97/4.49  
% 31.97/4.49  --out_options                           all
% 31.97/4.49  --tptp_safe_out                         true
% 31.97/4.49  --problem_path                          ""
% 31.97/4.49  --include_path                          ""
% 31.97/4.49  --clausifier                            res/vclausify_rel
% 31.97/4.49  --clausifier_options                    ""
% 31.97/4.49  --stdin                                 false
% 31.97/4.49  --stats_out                             all
% 31.97/4.49  
% 31.97/4.49  ------ General Options
% 31.97/4.49  
% 31.97/4.49  --fof                                   false
% 31.97/4.49  --time_out_real                         305.
% 31.97/4.49  --time_out_virtual                      -1.
% 31.97/4.49  --symbol_type_check                     false
% 31.97/4.49  --clausify_out                          false
% 31.97/4.49  --sig_cnt_out                           false
% 31.97/4.49  --trig_cnt_out                          false
% 31.97/4.49  --trig_cnt_out_tolerance                1.
% 31.97/4.49  --trig_cnt_out_sk_spl                   false
% 31.97/4.49  --abstr_cl_out                          false
% 31.97/4.49  
% 31.97/4.49  ------ Global Options
% 31.97/4.49  
% 31.97/4.49  --schedule                              default
% 31.97/4.49  --add_important_lit                     false
% 31.97/4.49  --prop_solver_per_cl                    1000
% 31.97/4.49  --min_unsat_core                        false
% 31.97/4.49  --soft_assumptions                      false
% 31.97/4.49  --soft_lemma_size                       3
% 31.97/4.49  --prop_impl_unit_size                   0
% 31.97/4.49  --prop_impl_unit                        []
% 31.97/4.49  --share_sel_clauses                     true
% 31.97/4.49  --reset_solvers                         false
% 31.97/4.49  --bc_imp_inh                            [conj_cone]
% 31.97/4.49  --conj_cone_tolerance                   3.
% 31.97/4.49  --extra_neg_conj                        none
% 31.97/4.49  --large_theory_mode                     true
% 31.97/4.49  --prolific_symb_bound                   200
% 31.97/4.49  --lt_threshold                          2000
% 31.97/4.49  --clause_weak_htbl                      true
% 31.97/4.49  --gc_record_bc_elim                     false
% 31.97/4.49  
% 31.97/4.49  ------ Preprocessing Options
% 31.97/4.49  
% 31.97/4.49  --preprocessing_flag                    true
% 31.97/4.49  --time_out_prep_mult                    0.1
% 31.97/4.49  --splitting_mode                        input
% 31.97/4.49  --splitting_grd                         true
% 31.97/4.49  --splitting_cvd                         false
% 31.97/4.49  --splitting_cvd_svl                     false
% 31.97/4.49  --splitting_nvd                         32
% 31.97/4.49  --sub_typing                            true
% 31.97/4.49  --prep_gs_sim                           true
% 31.97/4.49  --prep_unflatten                        true
% 31.97/4.49  --prep_res_sim                          true
% 31.97/4.49  --prep_upred                            true
% 31.97/4.49  --prep_sem_filter                       exhaustive
% 31.97/4.49  --prep_sem_filter_out                   false
% 31.97/4.49  --pred_elim                             true
% 31.97/4.49  --res_sim_input                         true
% 31.97/4.49  --eq_ax_congr_red                       true
% 31.97/4.49  --pure_diseq_elim                       true
% 31.97/4.49  --brand_transform                       false
% 31.97/4.49  --non_eq_to_eq                          false
% 31.97/4.49  --prep_def_merge                        true
% 31.97/4.49  --prep_def_merge_prop_impl              false
% 31.97/4.49  --prep_def_merge_mbd                    true
% 31.97/4.49  --prep_def_merge_tr_red                 false
% 31.97/4.49  --prep_def_merge_tr_cl                  false
% 31.97/4.49  --smt_preprocessing                     true
% 31.97/4.49  --smt_ac_axioms                         fast
% 31.97/4.49  --preprocessed_out                      false
% 31.97/4.49  --preprocessed_stats                    false
% 31.97/4.49  
% 31.97/4.49  ------ Abstraction refinement Options
% 31.97/4.49  
% 31.97/4.49  --abstr_ref                             []
% 31.97/4.49  --abstr_ref_prep                        false
% 31.97/4.49  --abstr_ref_until_sat                   false
% 31.97/4.49  --abstr_ref_sig_restrict                funpre
% 31.97/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.97/4.49  --abstr_ref_under                       []
% 31.97/4.49  
% 31.97/4.49  ------ SAT Options
% 31.97/4.49  
% 31.97/4.49  --sat_mode                              false
% 31.97/4.49  --sat_fm_restart_options                ""
% 31.97/4.49  --sat_gr_def                            false
% 31.97/4.49  --sat_epr_types                         true
% 31.97/4.49  --sat_non_cyclic_types                  false
% 31.97/4.49  --sat_finite_models                     false
% 31.97/4.49  --sat_fm_lemmas                         false
% 31.97/4.49  --sat_fm_prep                           false
% 31.97/4.49  --sat_fm_uc_incr                        true
% 31.97/4.49  --sat_out_model                         small
% 31.97/4.49  --sat_out_clauses                       false
% 31.97/4.49  
% 31.97/4.49  ------ QBF Options
% 31.97/4.49  
% 31.97/4.49  --qbf_mode                              false
% 31.97/4.49  --qbf_elim_univ                         false
% 31.97/4.49  --qbf_dom_inst                          none
% 31.97/4.49  --qbf_dom_pre_inst                      false
% 31.97/4.49  --qbf_sk_in                             false
% 31.97/4.49  --qbf_pred_elim                         true
% 31.97/4.49  --qbf_split                             512
% 31.97/4.49  
% 31.97/4.49  ------ BMC1 Options
% 31.97/4.49  
% 31.97/4.49  --bmc1_incremental                      false
% 31.97/4.49  --bmc1_axioms                           reachable_all
% 31.97/4.49  --bmc1_min_bound                        0
% 31.97/4.49  --bmc1_max_bound                        -1
% 31.97/4.49  --bmc1_max_bound_default                -1
% 31.97/4.49  --bmc1_symbol_reachability              true
% 31.97/4.49  --bmc1_property_lemmas                  false
% 31.97/4.49  --bmc1_k_induction                      false
% 31.97/4.49  --bmc1_non_equiv_states                 false
% 31.97/4.49  --bmc1_deadlock                         false
% 31.97/4.49  --bmc1_ucm                              false
% 31.97/4.49  --bmc1_add_unsat_core                   none
% 31.97/4.49  --bmc1_unsat_core_children              false
% 31.97/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.97/4.49  --bmc1_out_stat                         full
% 31.97/4.49  --bmc1_ground_init                      false
% 31.97/4.49  --bmc1_pre_inst_next_state              false
% 31.97/4.49  --bmc1_pre_inst_state                   false
% 31.97/4.49  --bmc1_pre_inst_reach_state             false
% 31.97/4.49  --bmc1_out_unsat_core                   false
% 31.97/4.49  --bmc1_aig_witness_out                  false
% 31.97/4.49  --bmc1_verbose                          false
% 31.97/4.49  --bmc1_dump_clauses_tptp                false
% 31.97/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.97/4.49  --bmc1_dump_file                        -
% 31.97/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.97/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.97/4.49  --bmc1_ucm_extend_mode                  1
% 31.97/4.49  --bmc1_ucm_init_mode                    2
% 31.97/4.49  --bmc1_ucm_cone_mode                    none
% 31.97/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.97/4.49  --bmc1_ucm_relax_model                  4
% 31.97/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.97/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.97/4.49  --bmc1_ucm_layered_model                none
% 31.97/4.49  --bmc1_ucm_max_lemma_size               10
% 31.97/4.49  
% 31.97/4.49  ------ AIG Options
% 31.97/4.49  
% 31.97/4.49  --aig_mode                              false
% 31.97/4.49  
% 31.97/4.49  ------ Instantiation Options
% 31.97/4.49  
% 31.97/4.49  --instantiation_flag                    true
% 31.97/4.49  --inst_sos_flag                         true
% 31.97/4.49  --inst_sos_phase                        true
% 31.97/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.97/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.97/4.49  --inst_lit_sel_side                     num_symb
% 31.97/4.49  --inst_solver_per_active                1400
% 31.97/4.49  --inst_solver_calls_frac                1.
% 31.97/4.49  --inst_passive_queue_type               priority_queues
% 31.97/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.97/4.49  --inst_passive_queues_freq              [25;2]
% 31.97/4.49  --inst_dismatching                      true
% 31.97/4.49  --inst_eager_unprocessed_to_passive     true
% 31.97/4.49  --inst_prop_sim_given                   true
% 31.97/4.49  --inst_prop_sim_new                     false
% 31.97/4.49  --inst_subs_new                         false
% 31.97/4.49  --inst_eq_res_simp                      false
% 31.97/4.49  --inst_subs_given                       false
% 31.97/4.49  --inst_orphan_elimination               true
% 31.97/4.49  --inst_learning_loop_flag               true
% 31.97/4.49  --inst_learning_start                   3000
% 31.97/4.49  --inst_learning_factor                  2
% 31.97/4.49  --inst_start_prop_sim_after_learn       3
% 31.97/4.49  --inst_sel_renew                        solver
% 31.97/4.49  --inst_lit_activity_flag                true
% 31.97/4.49  --inst_restr_to_given                   false
% 31.97/4.49  --inst_activity_threshold               500
% 31.97/4.49  --inst_out_proof                        true
% 31.97/4.49  
% 31.97/4.49  ------ Resolution Options
% 31.97/4.49  
% 31.97/4.49  --resolution_flag                       true
% 31.97/4.49  --res_lit_sel                           adaptive
% 31.97/4.49  --res_lit_sel_side                      none
% 31.97/4.49  --res_ordering                          kbo
% 31.97/4.49  --res_to_prop_solver                    active
% 31.97/4.49  --res_prop_simpl_new                    false
% 31.97/4.49  --res_prop_simpl_given                  true
% 31.97/4.49  --res_passive_queue_type                priority_queues
% 31.97/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.97/4.49  --res_passive_queues_freq               [15;5]
% 31.97/4.49  --res_forward_subs                      full
% 31.97/4.49  --res_backward_subs                     full
% 31.97/4.49  --res_forward_subs_resolution           true
% 31.97/4.49  --res_backward_subs_resolution          true
% 31.97/4.49  --res_orphan_elimination                true
% 31.97/4.49  --res_time_limit                        2.
% 31.97/4.49  --res_out_proof                         true
% 31.97/4.49  
% 31.97/4.49  ------ Superposition Options
% 31.97/4.49  
% 31.97/4.49  --superposition_flag                    true
% 31.97/4.49  --sup_passive_queue_type                priority_queues
% 31.97/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.97/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.97/4.49  --demod_completeness_check              fast
% 31.97/4.49  --demod_use_ground                      true
% 31.97/4.49  --sup_to_prop_solver                    passive
% 31.97/4.49  --sup_prop_simpl_new                    true
% 31.97/4.49  --sup_prop_simpl_given                  true
% 31.97/4.49  --sup_fun_splitting                     true
% 31.97/4.49  --sup_smt_interval                      50000
% 31.97/4.49  
% 31.97/4.49  ------ Superposition Simplification Setup
% 31.97/4.49  
% 31.97/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.97/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.97/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.97/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.97/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.97/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.97/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.97/4.49  --sup_immed_triv                        [TrivRules]
% 31.97/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.97/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.97/4.49  --sup_immed_bw_main                     []
% 31.97/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.97/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.97/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.97/4.49  --sup_input_bw                          []
% 31.97/4.49  
% 31.97/4.49  ------ Combination Options
% 31.97/4.49  
% 31.97/4.49  --comb_res_mult                         3
% 31.97/4.49  --comb_sup_mult                         2
% 31.97/4.49  --comb_inst_mult                        10
% 31.97/4.49  
% 31.97/4.49  ------ Debug Options
% 31.97/4.49  
% 31.97/4.49  --dbg_backtrace                         false
% 31.97/4.49  --dbg_dump_prop_clauses                 false
% 31.97/4.49  --dbg_dump_prop_clauses_file            -
% 31.97/4.49  --dbg_out_stat                          false
% 31.97/4.49  ------ Parsing...
% 31.97/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.97/4.49  
% 31.97/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 31.97/4.49  
% 31.97/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.97/4.49  
% 31.97/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.97/4.49  ------ Proving...
% 31.97/4.49  ------ Problem Properties 
% 31.97/4.49  
% 31.97/4.49  
% 31.97/4.49  clauses                                 30
% 31.97/4.49  conjectures                             2
% 31.97/4.49  EPR                                     4
% 31.97/4.49  Horn                                    30
% 31.97/4.49  unary                                   15
% 31.97/4.49  binary                                  11
% 31.97/4.49  lits                                    49
% 31.97/4.49  lits eq                                 17
% 31.97/4.49  fd_pure                                 0
% 31.97/4.49  fd_pseudo                               0
% 31.97/4.49  fd_cond                                 0
% 31.97/4.49  fd_pseudo_cond                          1
% 31.97/4.49  AC symbols                              0
% 31.97/4.49  
% 31.97/4.49  ------ Schedule dynamic 5 is on 
% 31.97/4.49  
% 31.97/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.97/4.49  
% 31.97/4.49  
% 31.97/4.49  ------ 
% 31.97/4.49  Current options:
% 31.97/4.49  ------ 
% 31.97/4.49  
% 31.97/4.49  ------ Input Options
% 31.97/4.49  
% 31.97/4.49  --out_options                           all
% 31.97/4.49  --tptp_safe_out                         true
% 31.97/4.49  --problem_path                          ""
% 31.97/4.49  --include_path                          ""
% 31.97/4.49  --clausifier                            res/vclausify_rel
% 31.97/4.49  --clausifier_options                    ""
% 31.97/4.49  --stdin                                 false
% 31.97/4.49  --stats_out                             all
% 31.97/4.49  
% 31.97/4.49  ------ General Options
% 31.97/4.49  
% 31.97/4.49  --fof                                   false
% 31.97/4.49  --time_out_real                         305.
% 31.97/4.49  --time_out_virtual                      -1.
% 31.97/4.49  --symbol_type_check                     false
% 31.97/4.49  --clausify_out                          false
% 31.97/4.49  --sig_cnt_out                           false
% 31.97/4.49  --trig_cnt_out                          false
% 31.97/4.49  --trig_cnt_out_tolerance                1.
% 31.97/4.49  --trig_cnt_out_sk_spl                   false
% 31.97/4.49  --abstr_cl_out                          false
% 31.97/4.49  
% 31.97/4.49  ------ Global Options
% 31.97/4.49  
% 31.97/4.49  --schedule                              default
% 31.97/4.49  --add_important_lit                     false
% 31.97/4.49  --prop_solver_per_cl                    1000
% 31.97/4.49  --min_unsat_core                        false
% 31.97/4.49  --soft_assumptions                      false
% 31.97/4.49  --soft_lemma_size                       3
% 31.97/4.49  --prop_impl_unit_size                   0
% 31.97/4.49  --prop_impl_unit                        []
% 31.97/4.49  --share_sel_clauses                     true
% 31.97/4.49  --reset_solvers                         false
% 31.97/4.49  --bc_imp_inh                            [conj_cone]
% 31.97/4.49  --conj_cone_tolerance                   3.
% 31.97/4.49  --extra_neg_conj                        none
% 31.97/4.49  --large_theory_mode                     true
% 31.97/4.49  --prolific_symb_bound                   200
% 31.97/4.49  --lt_threshold                          2000
% 31.97/4.49  --clause_weak_htbl                      true
% 31.97/4.49  --gc_record_bc_elim                     false
% 31.97/4.49  
% 31.97/4.49  ------ Preprocessing Options
% 31.97/4.49  
% 31.97/4.49  --preprocessing_flag                    true
% 31.97/4.49  --time_out_prep_mult                    0.1
% 31.97/4.49  --splitting_mode                        input
% 31.97/4.49  --splitting_grd                         true
% 31.97/4.49  --splitting_cvd                         false
% 31.97/4.49  --splitting_cvd_svl                     false
% 31.97/4.49  --splitting_nvd                         32
% 31.97/4.49  --sub_typing                            true
% 31.97/4.49  --prep_gs_sim                           true
% 31.97/4.49  --prep_unflatten                        true
% 31.97/4.49  --prep_res_sim                          true
% 31.97/4.49  --prep_upred                            true
% 31.97/4.49  --prep_sem_filter                       exhaustive
% 31.97/4.49  --prep_sem_filter_out                   false
% 31.97/4.49  --pred_elim                             true
% 31.97/4.49  --res_sim_input                         true
% 31.97/4.49  --eq_ax_congr_red                       true
% 31.97/4.49  --pure_diseq_elim                       true
% 31.97/4.49  --brand_transform                       false
% 31.97/4.49  --non_eq_to_eq                          false
% 31.97/4.49  --prep_def_merge                        true
% 31.97/4.49  --prep_def_merge_prop_impl              false
% 31.97/4.49  --prep_def_merge_mbd                    true
% 31.97/4.49  --prep_def_merge_tr_red                 false
% 31.97/4.49  --prep_def_merge_tr_cl                  false
% 31.97/4.49  --smt_preprocessing                     true
% 31.97/4.49  --smt_ac_axioms                         fast
% 31.97/4.49  --preprocessed_out                      false
% 31.97/4.49  --preprocessed_stats                    false
% 31.97/4.49  
% 31.97/4.49  ------ Abstraction refinement Options
% 31.97/4.49  
% 31.97/4.49  --abstr_ref                             []
% 31.97/4.49  --abstr_ref_prep                        false
% 31.97/4.49  --abstr_ref_until_sat                   false
% 31.97/4.49  --abstr_ref_sig_restrict                funpre
% 31.97/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.97/4.49  --abstr_ref_under                       []
% 31.97/4.49  
% 31.97/4.49  ------ SAT Options
% 31.97/4.49  
% 31.97/4.49  --sat_mode                              false
% 31.97/4.49  --sat_fm_restart_options                ""
% 31.97/4.49  --sat_gr_def                            false
% 31.97/4.49  --sat_epr_types                         true
% 31.97/4.49  --sat_non_cyclic_types                  false
% 31.97/4.49  --sat_finite_models                     false
% 31.97/4.49  --sat_fm_lemmas                         false
% 31.97/4.49  --sat_fm_prep                           false
% 31.97/4.49  --sat_fm_uc_incr                        true
% 31.97/4.49  --sat_out_model                         small
% 31.97/4.49  --sat_out_clauses                       false
% 31.97/4.49  
% 31.97/4.49  ------ QBF Options
% 31.97/4.49  
% 31.97/4.49  --qbf_mode                              false
% 31.97/4.49  --qbf_elim_univ                         false
% 31.97/4.49  --qbf_dom_inst                          none
% 31.97/4.49  --qbf_dom_pre_inst                      false
% 31.97/4.49  --qbf_sk_in                             false
% 31.97/4.49  --qbf_pred_elim                         true
% 31.97/4.49  --qbf_split                             512
% 31.97/4.49  
% 31.97/4.49  ------ BMC1 Options
% 31.97/4.49  
% 31.97/4.49  --bmc1_incremental                      false
% 31.97/4.49  --bmc1_axioms                           reachable_all
% 31.97/4.49  --bmc1_min_bound                        0
% 31.97/4.49  --bmc1_max_bound                        -1
% 31.97/4.49  --bmc1_max_bound_default                -1
% 31.97/4.49  --bmc1_symbol_reachability              true
% 31.97/4.49  --bmc1_property_lemmas                  false
% 31.97/4.49  --bmc1_k_induction                      false
% 31.97/4.49  --bmc1_non_equiv_states                 false
% 31.97/4.49  --bmc1_deadlock                         false
% 31.97/4.49  --bmc1_ucm                              false
% 31.97/4.49  --bmc1_add_unsat_core                   none
% 31.97/4.49  --bmc1_unsat_core_children              false
% 31.97/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.97/4.49  --bmc1_out_stat                         full
% 31.97/4.49  --bmc1_ground_init                      false
% 31.97/4.49  --bmc1_pre_inst_next_state              false
% 31.97/4.49  --bmc1_pre_inst_state                   false
% 31.97/4.49  --bmc1_pre_inst_reach_state             false
% 31.97/4.49  --bmc1_out_unsat_core                   false
% 31.97/4.49  --bmc1_aig_witness_out                  false
% 31.97/4.49  --bmc1_verbose                          false
% 31.97/4.49  --bmc1_dump_clauses_tptp                false
% 31.97/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.97/4.49  --bmc1_dump_file                        -
% 31.97/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.97/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.97/4.49  --bmc1_ucm_extend_mode                  1
% 31.97/4.49  --bmc1_ucm_init_mode                    2
% 31.97/4.49  --bmc1_ucm_cone_mode                    none
% 31.97/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.97/4.49  --bmc1_ucm_relax_model                  4
% 31.97/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.97/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.97/4.49  --bmc1_ucm_layered_model                none
% 31.97/4.49  --bmc1_ucm_max_lemma_size               10
% 31.97/4.49  
% 31.97/4.49  ------ AIG Options
% 31.97/4.49  
% 31.97/4.49  --aig_mode                              false
% 31.97/4.49  
% 31.97/4.49  ------ Instantiation Options
% 31.97/4.49  
% 31.97/4.49  --instantiation_flag                    true
% 31.97/4.49  --inst_sos_flag                         true
% 31.97/4.49  --inst_sos_phase                        true
% 31.97/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.97/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.97/4.49  --inst_lit_sel_side                     none
% 31.97/4.49  --inst_solver_per_active                1400
% 31.97/4.49  --inst_solver_calls_frac                1.
% 31.97/4.49  --inst_passive_queue_type               priority_queues
% 31.97/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.97/4.49  --inst_passive_queues_freq              [25;2]
% 31.97/4.49  --inst_dismatching                      true
% 31.97/4.49  --inst_eager_unprocessed_to_passive     true
% 31.97/4.49  --inst_prop_sim_given                   true
% 31.97/4.49  --inst_prop_sim_new                     false
% 31.97/4.49  --inst_subs_new                         false
% 31.97/4.49  --inst_eq_res_simp                      false
% 31.97/4.49  --inst_subs_given                       false
% 31.97/4.49  --inst_orphan_elimination               true
% 31.97/4.49  --inst_learning_loop_flag               true
% 31.97/4.49  --inst_learning_start                   3000
% 31.97/4.49  --inst_learning_factor                  2
% 31.97/4.49  --inst_start_prop_sim_after_learn       3
% 31.97/4.49  --inst_sel_renew                        solver
% 31.97/4.49  --inst_lit_activity_flag                true
% 31.97/4.49  --inst_restr_to_given                   false
% 31.97/4.49  --inst_activity_threshold               500
% 31.97/4.49  --inst_out_proof                        true
% 31.97/4.49  
% 31.97/4.49  ------ Resolution Options
% 31.97/4.49  
% 31.97/4.49  --resolution_flag                       false
% 31.97/4.49  --res_lit_sel                           adaptive
% 31.97/4.49  --res_lit_sel_side                      none
% 31.97/4.49  --res_ordering                          kbo
% 31.97/4.49  --res_to_prop_solver                    active
% 31.97/4.49  --res_prop_simpl_new                    false
% 31.97/4.49  --res_prop_simpl_given                  true
% 31.97/4.49  --res_passive_queue_type                priority_queues
% 31.97/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.97/4.49  --res_passive_queues_freq               [15;5]
% 31.97/4.49  --res_forward_subs                      full
% 31.97/4.49  --res_backward_subs                     full
% 31.97/4.49  --res_forward_subs_resolution           true
% 31.97/4.49  --res_backward_subs_resolution          true
% 31.97/4.49  --res_orphan_elimination                true
% 31.97/4.49  --res_time_limit                        2.
% 31.97/4.49  --res_out_proof                         true
% 31.97/4.49  
% 31.97/4.49  ------ Superposition Options
% 31.97/4.49  
% 31.97/4.49  --superposition_flag                    true
% 31.97/4.49  --sup_passive_queue_type                priority_queues
% 31.97/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.97/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.97/4.49  --demod_completeness_check              fast
% 31.97/4.49  --demod_use_ground                      true
% 31.97/4.49  --sup_to_prop_solver                    passive
% 31.97/4.49  --sup_prop_simpl_new                    true
% 31.97/4.49  --sup_prop_simpl_given                  true
% 31.97/4.49  --sup_fun_splitting                     true
% 31.97/4.49  --sup_smt_interval                      50000
% 31.97/4.49  
% 31.97/4.49  ------ Superposition Simplification Setup
% 31.97/4.49  
% 31.97/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.97/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.97/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.97/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.97/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.97/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.97/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.97/4.49  --sup_immed_triv                        [TrivRules]
% 31.97/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.97/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.97/4.49  --sup_immed_bw_main                     []
% 31.97/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.97/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.97/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.97/4.49  --sup_input_bw                          []
% 31.97/4.49  
% 31.97/4.49  ------ Combination Options
% 31.97/4.49  
% 31.97/4.49  --comb_res_mult                         3
% 31.97/4.49  --comb_sup_mult                         2
% 31.97/4.49  --comb_inst_mult                        10
% 31.97/4.49  
% 31.97/4.49  ------ Debug Options
% 31.97/4.49  
% 31.97/4.49  --dbg_backtrace                         false
% 31.97/4.49  --dbg_dump_prop_clauses                 false
% 31.97/4.49  --dbg_dump_prop_clauses_file            -
% 31.97/4.49  --dbg_out_stat                          false
% 31.97/4.49  
% 31.97/4.49  
% 31.97/4.49  
% 31.97/4.49  
% 31.97/4.49  ------ Proving...
% 31.97/4.49  
% 31.97/4.49  
% 31.97/4.49  % SZS status Theorem for theBenchmark.p
% 31.97/4.49  
% 31.97/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.97/4.49  
% 31.97/4.49  fof(f27,conjecture,(
% 31.97/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f28,negated_conjecture,(
% 31.97/4.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 31.97/4.49    inference(negated_conjecture,[],[f27])).
% 31.97/4.49  
% 31.97/4.49  fof(f43,plain,(
% 31.97/4.49    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 31.97/4.49    inference(ennf_transformation,[],[f28])).
% 31.97/4.49  
% 31.97/4.49  fof(f44,plain,(
% 31.97/4.49    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 31.97/4.49    inference(flattening,[],[f43])).
% 31.97/4.49  
% 31.97/4.49  fof(f50,plain,(
% 31.97/4.49    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),sK1) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.97/4.49    introduced(choice_axiom,[])).
% 31.97/4.49  
% 31.97/4.49  fof(f49,plain,(
% 31.97/4.49    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 31.97/4.49    introduced(choice_axiom,[])).
% 31.97/4.49  
% 31.97/4.49  fof(f51,plain,(
% 31.97/4.49    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 31.97/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f50,f49])).
% 31.97/4.49  
% 31.97/4.49  fof(f83,plain,(
% 31.97/4.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.97/4.49    inference(cnf_transformation,[],[f51])).
% 31.97/4.49  
% 31.97/4.49  fof(f25,axiom,(
% 31.97/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f41,plain,(
% 31.97/4.49    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.97/4.49    inference(ennf_transformation,[],[f25])).
% 31.97/4.49  
% 31.97/4.49  fof(f80,plain,(
% 31.97/4.49    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f41])).
% 31.97/4.49  
% 31.97/4.49  fof(f82,plain,(
% 31.97/4.49    l1_pre_topc(sK0)),
% 31.97/4.49    inference(cnf_transformation,[],[f51])).
% 31.97/4.49  
% 31.97/4.49  fof(f23,axiom,(
% 31.97/4.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f37,plain,(
% 31.97/4.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.97/4.49    inference(ennf_transformation,[],[f23])).
% 31.97/4.49  
% 31.97/4.49  fof(f38,plain,(
% 31.97/4.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.97/4.49    inference(flattening,[],[f37])).
% 31.97/4.49  
% 31.97/4.49  fof(f78,plain,(
% 31.97/4.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f38])).
% 31.97/4.49  
% 31.97/4.49  fof(f22,axiom,(
% 31.97/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f48,plain,(
% 31.97/4.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.97/4.49    inference(nnf_transformation,[],[f22])).
% 31.97/4.49  
% 31.97/4.49  fof(f76,plain,(
% 31.97/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.97/4.49    inference(cnf_transformation,[],[f48])).
% 31.97/4.49  
% 31.97/4.49  fof(f8,axiom,(
% 31.97/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f32,plain,(
% 31.97/4.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.97/4.49    inference(ennf_transformation,[],[f8])).
% 31.97/4.49  
% 31.97/4.49  fof(f62,plain,(
% 31.97/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f32])).
% 31.97/4.49  
% 31.97/4.49  fof(f15,axiom,(
% 31.97/4.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f69,plain,(
% 31.97/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f15])).
% 31.97/4.49  
% 31.97/4.49  fof(f21,axiom,(
% 31.97/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f75,plain,(
% 31.97/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.97/4.49    inference(cnf_transformation,[],[f21])).
% 31.97/4.49  
% 31.97/4.49  fof(f6,axiom,(
% 31.97/4.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f60,plain,(
% 31.97/4.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f6])).
% 31.97/4.49  
% 31.97/4.49  fof(f19,axiom,(
% 31.97/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f35,plain,(
% 31.97/4.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.97/4.49    inference(ennf_transformation,[],[f19])).
% 31.97/4.49  
% 31.97/4.49  fof(f36,plain,(
% 31.97/4.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.97/4.49    inference(flattening,[],[f35])).
% 31.97/4.49  
% 31.97/4.49  fof(f73,plain,(
% 31.97/4.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.97/4.49    inference(cnf_transformation,[],[f36])).
% 31.97/4.49  
% 31.97/4.49  fof(f77,plain,(
% 31.97/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f48])).
% 31.97/4.49  
% 31.97/4.49  fof(f26,axiom,(
% 31.97/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f42,plain,(
% 31.97/4.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.97/4.49    inference(ennf_transformation,[],[f26])).
% 31.97/4.49  
% 31.97/4.49  fof(f81,plain,(
% 31.97/4.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f42])).
% 31.97/4.49  
% 31.97/4.49  fof(f1,axiom,(
% 31.97/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f52,plain,(
% 31.97/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f1])).
% 31.97/4.49  
% 31.97/4.49  fof(f14,axiom,(
% 31.97/4.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f68,plain,(
% 31.97/4.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.97/4.49    inference(cnf_transformation,[],[f14])).
% 31.97/4.49  
% 31.97/4.49  fof(f5,axiom,(
% 31.97/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f29,plain,(
% 31.97/4.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 31.97/4.49    inference(ennf_transformation,[],[f5])).
% 31.97/4.49  
% 31.97/4.49  fof(f59,plain,(
% 31.97/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f29])).
% 31.97/4.49  
% 31.97/4.49  fof(f24,axiom,(
% 31.97/4.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f39,plain,(
% 31.97/4.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.97/4.49    inference(ennf_transformation,[],[f24])).
% 31.97/4.49  
% 31.97/4.49  fof(f40,plain,(
% 31.97/4.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.97/4.49    inference(flattening,[],[f39])).
% 31.97/4.49  
% 31.97/4.49  fof(f79,plain,(
% 31.97/4.49    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.97/4.49    inference(cnf_transformation,[],[f40])).
% 31.97/4.49  
% 31.97/4.49  fof(f84,plain,(
% 31.97/4.49    v4_pre_topc(sK1,sK0)),
% 31.97/4.49    inference(cnf_transformation,[],[f51])).
% 31.97/4.49  
% 31.97/4.49  fof(f2,axiom,(
% 31.97/4.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.97/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.97/4.49  
% 31.97/4.49  fof(f45,plain,(
% 31.97/4.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.97/4.49    inference(nnf_transformation,[],[f2])).
% 31.97/4.49  
% 31.97/4.49  fof(f46,plain,(
% 31.97/4.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.97/4.49    inference(flattening,[],[f45])).
% 31.97/4.49  
% 31.97/4.49  fof(f53,plain,(
% 31.97/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.97/4.49    inference(cnf_transformation,[],[f46])).
% 31.97/4.49  
% 31.97/4.49  fof(f95,plain,(
% 31.97/4.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.97/4.49    inference(equality_resolution,[],[f53])).
% 31.97/4.49  
% 31.97/4.49  fof(f85,plain,(
% 31.97/4.49    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 31.97/4.49    inference(cnf_transformation,[],[f51])).
% 31.97/4.49  
% 31.97/4.49  cnf(c_31,negated_conjecture,
% 31.97/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.97/4.49      inference(cnf_transformation,[],[f83]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1146,plain,
% 31.97/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_27,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | ~ l1_pre_topc(X1)
% 31.97/4.49      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 31.97/4.49      inference(cnf_transformation,[],[f80]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_32,negated_conjecture,
% 31.97/4.49      ( l1_pre_topc(sK0) ),
% 31.97/4.49      inference(cnf_transformation,[],[f82]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_391,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
% 31.97/4.49      | sK0 != X1 ),
% 31.97/4.49      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_392,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.97/4.49      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
% 31.97/4.49      inference(unflattening,[status(thm)],[c_391]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1141,plain,
% 31.97/4.49      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0)
% 31.97/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1452,plain,
% 31.97/4.49      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1146,c_1141]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_25,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | ~ l1_pre_topc(X1) ),
% 31.97/4.49      inference(cnf_transformation,[],[f78]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_403,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | sK0 != X1 ),
% 31.97/4.49      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_404,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.97/4.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.97/4.49      inference(unflattening,[status(thm)],[c_403]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1140,plain,
% 31.97/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.97/4.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1546,plain,
% 31.97/4.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 31.97/4.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1452,c_1140]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_34,plain,
% 31.97/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1219,plain,
% 31.97/4.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.97/4.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.97/4.49      inference(instantiation,[status(thm)],[c_404]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1220,plain,
% 31.97/4.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 31.97/4.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_1219]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_2116,plain,
% 31.97/4.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.97/4.49      inference(global_propositional_subsumption,
% 31.97/4.49                [status(thm)],
% 31.97/4.49                [c_1546,c_34,c_1220]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_24,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.97/4.49      inference(cnf_transformation,[],[f76]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1148,plain,
% 31.97/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.97/4.49      | r1_tarski(X0,X1) = iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_3162,plain,
% 31.97/4.49      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_2116,c_1148]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_10,plain,
% 31.97/4.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 31.97/4.49      inference(cnf_transformation,[],[f62]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1153,plain,
% 31.97/4.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_20546,plain,
% 31.97/4.49      ( k3_xboole_0(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = k2_tops_1(sK0,sK1) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_3162,c_1153]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_16,plain,
% 31.97/4.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 31.97/4.49      inference(cnf_transformation,[],[f69]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_22,plain,
% 31.97/4.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 31.97/4.49      inference(cnf_transformation,[],[f75]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1949,plain,
% 31.97/4.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_16,c_22]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_4174,plain,
% 31.97/4.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1949,c_22]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_54554,plain,
% 31.97/4.49      ( k3_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_20546,c_4174]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_3160,plain,
% 31.97/4.49      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1146,c_1148]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_8,plain,
% 31.97/4.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 31.97/4.49      inference(cnf_transformation,[],[f60]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1155,plain,
% 31.97/4.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_20,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.97/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.97/4.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.97/4.49      inference(cnf_transformation,[],[f73]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_23,plain,
% 31.97/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.97/4.49      inference(cnf_transformation,[],[f77]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_211,plain,
% 31.97/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.97/4.49      inference(prop_impl,[status(thm)],[c_23]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_212,plain,
% 31.97/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.97/4.49      inference(renaming,[status(thm)],[c_211]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_259,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.97/4.49      | ~ r1_tarski(X2,X1)
% 31.97/4.49      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.97/4.49      inference(bin_hyper_res,[status(thm)],[c_20,c_212]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_507,plain,
% 31.97/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.97/4.49      inference(prop_impl,[status(thm)],[c_23]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_508,plain,
% 31.97/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.97/4.49      inference(renaming,[status(thm)],[c_507]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_550,plain,
% 31.97/4.49      ( ~ r1_tarski(X0,X1)
% 31.97/4.49      | ~ r1_tarski(X2,X1)
% 31.97/4.49      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.97/4.49      inference(bin_hyper_res,[status(thm)],[c_259,c_508]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1139,plain,
% 31.97/4.49      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 31.97/4.49      | r1_tarski(X2,X0) != iProver_top
% 31.97/4.49      | r1_tarski(X1,X0) != iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_3312,plain,
% 31.97/4.49      ( k4_subset_1(X0,X1,k3_xboole_0(X0,X2)) = k2_xboole_0(X1,k3_xboole_0(X0,X2))
% 31.97/4.49      | r1_tarski(X1,X0) != iProver_top ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1155,c_1139]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_50093,plain,
% 31.97/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(u1_struct_0(sK0),X0)) = k2_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),X0)) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_3160,c_3312]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_56035,plain,
% 31.97/4.49      ( k2_xboole_0(sK1,k3_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_54554,c_50093]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_56036,plain,
% 31.97/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 31.97/4.49      inference(demodulation,[status(thm)],[c_56035,c_54554]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_28,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | ~ l1_pre_topc(X1)
% 31.97/4.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 31.97/4.49      inference(cnf_transformation,[],[f81]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_379,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 31.97/4.49      | sK0 != X1 ),
% 31.97/4.49      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_380,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.97/4.49      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 31.97/4.49      inference(unflattening,[status(thm)],[c_379]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1142,plain,
% 31.97/4.49      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 31.97/4.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1549,plain,
% 31.97/4.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1146,c_1142]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_56037,plain,
% 31.97/4.49      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.97/4.49      inference(light_normalisation,[status(thm)],[c_56036,c_1549]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1,plain,
% 31.97/4.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 31.97/4.49      inference(cnf_transformation,[],[f52]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_15,plain,
% 31.97/4.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 31.97/4.49      inference(cnf_transformation,[],[f68]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1151,plain,
% 31.97/4.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_3174,plain,
% 31.97/4.49      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1,c_1151]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_56177,plain,
% 31.97/4.49      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_56037,c_3174]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_7,plain,
% 31.97/4.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 31.97/4.49      inference(cnf_transformation,[],[f59]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1156,plain,
% 31.97/4.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_6161,plain,
% 31.97/4.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1151,c_1156]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_56163,plain,
% 31.97/4.49      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_56037,c_6161]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_56188,plain,
% 31.97/4.49      ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 31.97/4.49      inference(demodulation,[status(thm)],[c_56163,c_56037]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_26,plain,
% 31.97/4.49      ( ~ v4_pre_topc(X0,X1)
% 31.97/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | ~ r1_tarski(X2,X0)
% 31.97/4.49      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 31.97/4.49      | ~ l1_pre_topc(X1) ),
% 31.97/4.49      inference(cnf_transformation,[],[f79]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_30,negated_conjecture,
% 31.97/4.49      ( v4_pre_topc(sK1,sK0) ),
% 31.97/4.49      inference(cnf_transformation,[],[f84]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_354,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.97/4.49      | ~ r1_tarski(X2,X0)
% 31.97/4.49      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 31.97/4.49      | ~ l1_pre_topc(X1)
% 31.97/4.49      | sK1 != X0
% 31.97/4.49      | sK0 != X1 ),
% 31.97/4.49      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_355,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.97/4.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.97/4.49      | ~ r1_tarski(X0,sK1)
% 31.97/4.49      | r1_tarski(k2_pre_topc(sK0,X0),sK1)
% 31.97/4.49      | ~ l1_pre_topc(sK0) ),
% 31.97/4.49      inference(unflattening,[status(thm)],[c_354]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_359,plain,
% 31.97/4.49      ( r1_tarski(k2_pre_topc(sK0,X0),sK1)
% 31.97/4.49      | ~ r1_tarski(X0,sK1)
% 31.97/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.97/4.49      inference(global_propositional_subsumption,
% 31.97/4.49                [status(thm)],
% 31.97/4.49                [c_355,c_32,c_31]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_360,plain,
% 31.97/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.97/4.49      | ~ r1_tarski(X0,sK1)
% 31.97/4.49      | r1_tarski(k2_pre_topc(sK0,X0),sK1) ),
% 31.97/4.49      inference(renaming,[status(thm)],[c_359]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1143,plain,
% 31.97/4.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.97/4.49      | r1_tarski(X0,sK1) != iProver_top
% 31.97/4.49      | r1_tarski(k2_pre_topc(sK0,X0),sK1) = iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1629,plain,
% 31.97/4.49      ( r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top
% 31.97/4.49      | r1_tarski(sK1,sK1) != iProver_top ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1146,c_1143]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1294,plain,
% 31.97/4.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.97/4.49      | r1_tarski(k2_pre_topc(sK0,sK1),sK1)
% 31.97/4.49      | ~ r1_tarski(sK1,sK1) ),
% 31.97/4.49      inference(instantiation,[status(thm)],[c_360]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1295,plain,
% 31.97/4.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.97/4.49      | r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top
% 31.97/4.49      | r1_tarski(sK1,sK1) != iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_4,plain,
% 31.97/4.49      ( r1_tarski(X0,X0) ),
% 31.97/4.49      inference(cnf_transformation,[],[f95]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1404,plain,
% 31.97/4.49      ( r1_tarski(sK1,sK1) ),
% 31.97/4.49      inference(instantiation,[status(thm)],[c_4]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1405,plain,
% 31.97/4.49      ( r1_tarski(sK1,sK1) = iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_1952,plain,
% 31.97/4.49      ( r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top ),
% 31.97/4.49      inference(global_propositional_subsumption,
% 31.97/4.49                [status(thm)],
% 31.97/4.49                [c_1629,c_34,c_1295,c_1405]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_6165,plain,
% 31.97/4.49      ( k2_xboole_0(k2_pre_topc(sK0,sK1),sK1) = sK1 ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_1952,c_1156]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_6783,plain,
% 31.97/4.49      ( k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = sK1 ),
% 31.97/4.49      inference(superposition,[status(thm)],[c_6165,c_1]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_56189,plain,
% 31.97/4.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 31.97/4.49      inference(light_normalisation,[status(thm)],[c_56188,c_6783]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_56391,plain,
% 31.97/4.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 31.97/4.49      inference(light_normalisation,[status(thm)],[c_56177,c_56189]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_29,negated_conjecture,
% 31.97/4.49      ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
% 31.97/4.49      inference(cnf_transformation,[],[f85]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(c_36,plain,
% 31.97/4.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 31.97/4.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.97/4.49  
% 31.97/4.49  cnf(contradiction,plain,
% 31.97/4.49      ( $false ),
% 31.97/4.49      inference(minisat,[status(thm)],[c_56391,c_36]) ).
% 31.97/4.49  
% 31.97/4.49  
% 31.97/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.97/4.49  
% 31.97/4.49  ------                               Statistics
% 31.97/4.49  
% 31.97/4.49  ------ General
% 31.97/4.49  
% 31.97/4.49  abstr_ref_over_cycles:                  0
% 31.97/4.49  abstr_ref_under_cycles:                 0
% 31.97/4.49  gc_basic_clause_elim:                   0
% 31.97/4.49  forced_gc_time:                         0
% 31.97/4.49  parsing_time:                           0.006
% 31.97/4.49  unif_index_cands_time:                  0.
% 31.97/4.49  unif_index_add_time:                    0.
% 31.97/4.49  orderings_time:                         0.
% 31.97/4.49  out_proof_time:                         0.012
% 31.97/4.49  total_time:                             4.001
% 31.97/4.49  num_of_symbols:                         50
% 31.97/4.49  num_of_terms:                           46644
% 31.97/4.49  
% 31.97/4.49  ------ Preprocessing
% 31.97/4.49  
% 31.97/4.49  num_of_splits:                          0
% 31.97/4.49  num_of_split_atoms:                     0
% 31.97/4.49  num_of_reused_defs:                     0
% 31.97/4.49  num_eq_ax_congr_red:                    25
% 31.97/4.49  num_of_sem_filtered_clauses:            1
% 31.97/4.49  num_of_subtypes:                        0
% 31.97/4.49  monotx_restored_types:                  0
% 31.97/4.49  sat_num_of_epr_types:                   0
% 31.97/4.49  sat_num_of_non_cyclic_types:            0
% 31.97/4.49  sat_guarded_non_collapsed_types:        0
% 31.97/4.49  num_pure_diseq_elim:                    0
% 31.97/4.49  simp_replaced_by:                       0
% 31.97/4.49  res_preprocessed:                       151
% 31.97/4.49  prep_upred:                             0
% 31.97/4.49  prep_unflattend:                        5
% 31.97/4.49  smt_new_axioms:                         0
% 31.97/4.49  pred_elim_cands:                        2
% 31.97/4.49  pred_elim:                              2
% 31.97/4.49  pred_elim_cl:                           2
% 31.97/4.49  pred_elim_cycles:                       4
% 31.97/4.49  merged_defs:                            16
% 31.97/4.49  merged_defs_ncl:                        0
% 31.97/4.49  bin_hyper_res:                          20
% 31.97/4.49  prep_cycles:                            4
% 31.97/4.49  pred_elim_time:                         0.001
% 31.97/4.49  splitting_time:                         0.
% 31.97/4.49  sem_filter_time:                        0.
% 31.97/4.49  monotx_time:                            0.
% 31.97/4.49  subtype_inf_time:                       0.
% 31.97/4.49  
% 31.97/4.49  ------ Problem properties
% 31.97/4.49  
% 31.97/4.49  clauses:                                30
% 31.97/4.49  conjectures:                            2
% 31.97/4.49  epr:                                    4
% 31.97/4.49  horn:                                   30
% 31.97/4.49  ground:                                 2
% 31.97/4.49  unary:                                  15
% 31.97/4.49  binary:                                 11
% 31.97/4.49  lits:                                   49
% 31.97/4.49  lits_eq:                                17
% 31.97/4.49  fd_pure:                                0
% 31.97/4.49  fd_pseudo:                              0
% 31.97/4.49  fd_cond:                                0
% 31.97/4.49  fd_pseudo_cond:                         1
% 31.97/4.49  ac_symbols:                             0
% 31.97/4.49  
% 31.97/4.49  ------ Propositional Solver
% 31.97/4.49  
% 31.97/4.49  prop_solver_calls:                      31
% 31.97/4.49  prop_fast_solver_calls:                 1320
% 31.97/4.49  smt_solver_calls:                       0
% 31.97/4.49  smt_fast_solver_calls:                  0
% 31.97/4.49  prop_num_of_clauses:                    24146
% 31.97/4.49  prop_preprocess_simplified:             41134
% 31.97/4.49  prop_fo_subsumed:                       9
% 31.97/4.49  prop_solver_time:                       0.
% 31.97/4.49  smt_solver_time:                        0.
% 31.97/4.49  smt_fast_solver_time:                   0.
% 31.97/4.49  prop_fast_solver_time:                  0.
% 31.97/4.49  prop_unsat_core_time:                   0.002
% 31.97/4.49  
% 31.97/4.49  ------ QBF
% 31.97/4.49  
% 31.97/4.49  qbf_q_res:                              0
% 31.97/4.49  qbf_num_tautologies:                    0
% 31.97/4.49  qbf_prep_cycles:                        0
% 31.97/4.49  
% 31.97/4.49  ------ BMC1
% 31.97/4.49  
% 31.97/4.49  bmc1_current_bound:                     -1
% 31.97/4.49  bmc1_last_solved_bound:                 -1
% 31.97/4.49  bmc1_unsat_core_size:                   -1
% 31.97/4.49  bmc1_unsat_core_parents_size:           -1
% 31.97/4.49  bmc1_merge_next_fun:                    0
% 31.97/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.97/4.49  
% 31.97/4.49  ------ Instantiation
% 31.97/4.49  
% 31.97/4.49  inst_num_of_clauses:                    5771
% 31.97/4.49  inst_num_in_passive:                    2598
% 31.97/4.49  inst_num_in_active:                     1980
% 31.97/4.49  inst_num_in_unprocessed:                1193
% 31.97/4.49  inst_num_of_loops:                      2150
% 31.97/4.49  inst_num_of_learning_restarts:          0
% 31.97/4.49  inst_num_moves_active_passive:          170
% 31.97/4.49  inst_lit_activity:                      0
% 31.97/4.49  inst_lit_activity_moves:                0
% 31.97/4.49  inst_num_tautologies:                   0
% 31.97/4.49  inst_num_prop_implied:                  0
% 31.97/4.49  inst_num_existing_simplified:           0
% 31.97/4.49  inst_num_eq_res_simplified:             0
% 31.97/4.49  inst_num_child_elim:                    0
% 31.97/4.49  inst_num_of_dismatching_blockings:      2401
% 31.97/4.49  inst_num_of_non_proper_insts:           7305
% 31.97/4.49  inst_num_of_duplicates:                 0
% 31.97/4.49  inst_inst_num_from_inst_to_res:         0
% 31.97/4.49  inst_dismatching_checking_time:         0.
% 31.97/4.49  
% 31.97/4.49  ------ Resolution
% 31.97/4.49  
% 31.97/4.49  res_num_of_clauses:                     0
% 31.97/4.49  res_num_in_passive:                     0
% 31.97/4.49  res_num_in_active:                      0
% 31.97/4.49  res_num_of_loops:                       155
% 31.97/4.49  res_forward_subset_subsumed:            784
% 31.97/4.49  res_backward_subset_subsumed:           0
% 31.97/4.49  res_forward_subsumed:                   0
% 31.97/4.49  res_backward_subsumed:                  0
% 31.97/4.49  res_forward_subsumption_resolution:     0
% 31.97/4.49  res_backward_subsumption_resolution:    0
% 31.97/4.49  res_clause_to_clause_subsumption:       33033
% 31.97/4.49  res_orphan_elimination:                 0
% 31.97/4.49  res_tautology_del:                      715
% 31.97/4.49  res_num_eq_res_simplified:              0
% 31.97/4.49  res_num_sel_changes:                    0
% 31.97/4.49  res_moves_from_active_to_pass:          0
% 31.97/4.49  
% 31.97/4.49  ------ Superposition
% 31.97/4.49  
% 31.97/4.49  sup_time_total:                         0.
% 31.97/4.49  sup_time_generating:                    0.
% 31.97/4.49  sup_time_sim_full:                      0.
% 31.97/4.49  sup_time_sim_immed:                     0.
% 31.97/4.49  
% 31.97/4.49  sup_num_of_clauses:                     2589
% 31.97/4.49  sup_num_in_active:                      417
% 31.97/4.49  sup_num_in_passive:                     2172
% 31.97/4.49  sup_num_of_loops:                       428
% 31.97/4.49  sup_fw_superposition:                   4628
% 31.97/4.49  sup_bw_superposition:                   1809
% 31.97/4.49  sup_immediate_simplified:               1557
% 31.97/4.49  sup_given_eliminated:                   2
% 31.97/4.49  comparisons_done:                       0
% 31.97/4.49  comparisons_avoided:                    0
% 31.97/4.49  
% 31.97/4.49  ------ Simplifications
% 31.97/4.49  
% 31.97/4.49  
% 31.97/4.49  sim_fw_subset_subsumed:                 17
% 31.97/4.49  sim_bw_subset_subsumed:                 1
% 31.97/4.49  sim_fw_subsumed:                        308
% 31.97/4.49  sim_bw_subsumed:                        5
% 31.97/4.49  sim_fw_subsumption_res:                 0
% 31.97/4.49  sim_bw_subsumption_res:                 0
% 31.97/4.49  sim_tautology_del:                      2
% 31.97/4.49  sim_eq_tautology_del:                   249
% 31.97/4.49  sim_eq_res_simp:                        0
% 31.97/4.49  sim_fw_demodulated:                     329
% 31.97/4.49  sim_bw_demodulated:                     30
% 31.97/4.49  sim_light_normalised:                   1091
% 31.97/4.49  sim_joinable_taut:                      0
% 31.97/4.49  sim_joinable_simp:                      0
% 31.97/4.49  sim_ac_normalised:                      0
% 31.97/4.49  sim_smt_subsumption:                    0
% 31.97/4.49  
%------------------------------------------------------------------------------
