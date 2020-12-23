%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:43 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 293 expanded)
%              Number of clauses        :   67 ( 104 expanded)
%              Number of leaves         :   15 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  276 ( 941 expanded)
%              Number of equality atoms :  114 ( 152 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28,f27])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_712,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_715,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_719,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1308,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) = k2_pre_topc(X0,k1_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_719])).

cnf(c_4680,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_1308])).

cnf(c_11,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_716,plain,
    ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
    | v5_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1441,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | v5_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_716])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_928,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1590,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1441,c_16,c_15,c_14,c_928])).

cnf(c_4698,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4680,c_1590])).

cnf(c_17,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4852,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4698,c_17])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_718,plain,
    ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2245,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_718])).

cnf(c_934,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2532,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2245,c_16,c_15,c_934])).

cnf(c_4855,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4852,c_2532])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_720,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_942,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_720])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_115,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_115])).

cnf(c_140,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_116])).

cnf(c_710,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_2057,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(superposition,[status(thm)],[c_942,c_710])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_142,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_116])).

cnf(c_708,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_1155,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_942,c_708])).

cnf(c_2059,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,X0) = k3_xboole_0(X0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2057,c_1155])).

cnf(c_4864,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4855,c_2059])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_722,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1154,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_722,c_708])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_141,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_116])).

cnf(c_709,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_1868,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_709])).

cnf(c_8606,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1868,c_722])).

cnf(c_8612,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4864,c_8606])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_889,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_1053,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | k2_tops_1(sK0,sK1) != X0
    | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1725,plain,
    ( ~ m1_subset_1(k2_tops_1(X0,sK1),k1_zfmisc_1(X1))
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | k2_tops_1(sK0,sK1) != k2_tops_1(X0,sK1)
    | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_5534,plain,
    ( ~ m1_subset_1(k2_tops_1(X0,sK1),k1_zfmisc_1(sK1))
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | k2_tops_1(sK0,sK1) != k2_tops_1(X0,sK1)
    | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_5535,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(X0,sK1)
    | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(sK1)
    | m1_subset_1(k2_tops_1(X0,sK1),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5534])).

cnf(c_5537,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(sK1)
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5535])).

cnf(c_315,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1737,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0
    | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_3219,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != sK1
    | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_311,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_988,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_842,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_843,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8612,c_5537,c_3219,c_988,c_928,c_843,c_20,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.95/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/1.00  
% 3.95/1.00  ------  iProver source info
% 3.95/1.00  
% 3.95/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.95/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/1.00  git: non_committed_changes: false
% 3.95/1.00  git: last_make_outside_of_git: false
% 3.95/1.00  
% 3.95/1.00  ------ 
% 3.95/1.00  ------ Parsing...
% 3.95/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/1.00  
% 3.95/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/1.00  ------ Proving...
% 3.95/1.00  ------ Problem Properties 
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  clauses                                 16
% 3.95/1.00  conjectures                             4
% 3.95/1.00  EPR                                     4
% 3.95/1.00  Horn                                    16
% 3.95/1.00  unary                                   5
% 3.95/1.00  binary                                  5
% 3.95/1.00  lits                                    35
% 3.95/1.00  lits eq                                 7
% 3.95/1.00  fd_pure                                 0
% 3.95/1.00  fd_pseudo                               0
% 3.95/1.00  fd_cond                                 0
% 3.95/1.00  fd_pseudo_cond                          1
% 3.95/1.00  AC symbols                              0
% 3.95/1.00  
% 3.95/1.00  ------ Input Options Time Limit: Unbounded
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ 
% 3.95/1.00  Current options:
% 3.95/1.00  ------ 
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  ------ Proving...
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  % SZS status Theorem for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  fof(f10,conjecture,(
% 3.95/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f11,negated_conjecture,(
% 3.95/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.95/1.00    inference(negated_conjecture,[],[f10])).
% 3.95/1.00  
% 3.95/1.00  fof(f21,plain,(
% 3.95/1.00    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.95/1.00    inference(ennf_transformation,[],[f11])).
% 3.95/1.00  
% 3.95/1.00  fof(f22,plain,(
% 3.95/1.00    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.95/1.00    inference(flattening,[],[f21])).
% 3.95/1.00  
% 3.95/1.00  fof(f28,plain,(
% 3.95/1.00    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.95/1.00    introduced(choice_axiom,[])).
% 3.95/1.00  
% 3.95/1.00  fof(f27,plain,(
% 3.95/1.00    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.95/1.00    introduced(choice_axiom,[])).
% 3.95/1.00  
% 3.95/1.00  fof(f29,plain,(
% 3.95/1.00    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28,f27])).
% 3.95/1.00  
% 3.95/1.00  fof(f44,plain,(
% 3.95/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.95/1.00    inference(cnf_transformation,[],[f29])).
% 3.95/1.00  
% 3.95/1.00  fof(f9,axiom,(
% 3.95/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f19,plain,(
% 3.95/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.95/1.00    inference(ennf_transformation,[],[f9])).
% 3.95/1.00  
% 3.95/1.00  fof(f20,plain,(
% 3.95/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.95/1.00    inference(flattening,[],[f19])).
% 3.95/1.00  
% 3.95/1.00  fof(f42,plain,(
% 3.95/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f20])).
% 3.95/1.00  
% 3.95/1.00  fof(f6,axiom,(
% 3.95/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f15,plain,(
% 3.95/1.00    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.95/1.00    inference(ennf_transformation,[],[f6])).
% 3.95/1.00  
% 3.95/1.00  fof(f16,plain,(
% 3.95/1.00    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.95/1.00    inference(flattening,[],[f15])).
% 3.95/1.00  
% 3.95/1.00  fof(f38,plain,(
% 3.95/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f16])).
% 3.95/1.00  
% 3.95/1.00  fof(f8,axiom,(
% 3.95/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f18,plain,(
% 3.95/1.00    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/1.00    inference(ennf_transformation,[],[f8])).
% 3.95/1.00  
% 3.95/1.00  fof(f26,plain,(
% 3.95/1.00    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/1.00    inference(nnf_transformation,[],[f18])).
% 3.95/1.00  
% 3.95/1.00  fof(f40,plain,(
% 3.95/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f26])).
% 3.95/1.00  
% 3.95/1.00  fof(f43,plain,(
% 3.95/1.00    l1_pre_topc(sK0)),
% 3.95/1.00    inference(cnf_transformation,[],[f29])).
% 3.95/1.00  
% 3.95/1.00  fof(f45,plain,(
% 3.95/1.00    v5_tops_1(sK1,sK0)),
% 3.95/1.00    inference(cnf_transformation,[],[f29])).
% 3.95/1.00  
% 3.95/1.00  fof(f7,axiom,(
% 3.95/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f17,plain,(
% 3.95/1.00    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/1.00    inference(ennf_transformation,[],[f7])).
% 3.95/1.00  
% 3.95/1.00  fof(f39,plain,(
% 3.95/1.00    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f17])).
% 3.95/1.00  
% 3.95/1.00  fof(f5,axiom,(
% 3.95/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f25,plain,(
% 3.95/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.95/1.00    inference(nnf_transformation,[],[f5])).
% 3.95/1.00  
% 3.95/1.00  fof(f36,plain,(
% 3.95/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f25])).
% 3.95/1.00  
% 3.95/1.00  fof(f2,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f12,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.95/1.00    inference(ennf_transformation,[],[f2])).
% 3.95/1.00  
% 3.95/1.00  fof(f33,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f12])).
% 3.95/1.00  
% 3.95/1.00  fof(f37,plain,(
% 3.95/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.95/1.00    inference(cnf_transformation,[],[f25])).
% 3.95/1.00  
% 3.95/1.00  fof(f4,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f14,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.95/1.00    inference(ennf_transformation,[],[f4])).
% 3.95/1.00  
% 3.95/1.00  fof(f35,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f14])).
% 3.95/1.00  
% 3.95/1.00  fof(f1,axiom,(
% 3.95/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f23,plain,(
% 3.95/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.95/1.00    inference(nnf_transformation,[],[f1])).
% 3.95/1.00  
% 3.95/1.00  fof(f24,plain,(
% 3.95/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.95/1.00    inference(flattening,[],[f23])).
% 3.95/1.00  
% 3.95/1.00  fof(f31,plain,(
% 3.95/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.95/1.00    inference(cnf_transformation,[],[f24])).
% 3.95/1.00  
% 3.95/1.00  fof(f47,plain,(
% 3.95/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.95/1.00    inference(equality_resolution,[],[f31])).
% 3.95/1.00  
% 3.95/1.00  fof(f3,axiom,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.00  
% 3.95/1.00  fof(f13,plain,(
% 3.95/1.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.95/1.00    inference(ennf_transformation,[],[f3])).
% 3.95/1.00  
% 3.95/1.00  fof(f34,plain,(
% 3.95/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.95/1.00    inference(cnf_transformation,[],[f13])).
% 3.95/1.00  
% 3.95/1.00  fof(f46,plain,(
% 3.95/1.00    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 3.95/1.00    inference(cnf_transformation,[],[f29])).
% 3.95/1.00  
% 3.95/1.00  cnf(c_15,negated_conjecture,
% 3.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.95/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_712,plain,
% 3.95/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_12,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/1.00      | ~ l1_pre_topc(X1) ),
% 3.95/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_715,plain,
% 3.95/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.95/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.95/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/1.00      | ~ l1_pre_topc(X1)
% 3.95/1.00      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_719,plain,
% 3.95/1.00      ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
% 3.95/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.95/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1308,plain,
% 3.95/1.00      ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) = k2_pre_topc(X0,k1_tops_1(X0,X1))
% 3.95/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.95/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_715,c_719]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4680,plain,
% 3.95/1.00      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 3.95/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_712,c_1308]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_11,plain,
% 3.95/1.00      ( ~ v5_tops_1(X0,X1)
% 3.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/1.00      | ~ l1_pre_topc(X1)
% 3.95/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.95/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_716,plain,
% 3.95/1.00      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
% 3.95/1.00      | v5_tops_1(X1,X0) != iProver_top
% 3.95/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.95/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1441,plain,
% 3.95/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
% 3.95/1.00      | v5_tops_1(sK1,sK0) != iProver_top
% 3.95/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_712,c_716]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_16,negated_conjecture,
% 3.95/1.00      ( l1_pre_topc(sK0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_14,negated_conjecture,
% 3.95/1.00      ( v5_tops_1(sK1,sK0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_928,plain,
% 3.95/1.00      ( ~ v5_tops_1(sK1,sK0)
% 3.95/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.95/1.00      | ~ l1_pre_topc(sK0)
% 3.95/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1590,plain,
% 3.95/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_1441,c_16,c_15,c_14,c_928]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4698,plain,
% 3.95/1.00      ( k2_pre_topc(sK0,sK1) = sK1 | l1_pre_topc(sK0) != iProver_top ),
% 3.95/1.00      inference(light_normalisation,[status(thm)],[c_4680,c_1590]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_17,plain,
% 3.95/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4852,plain,
% 3.95/1.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_4698,c_17]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_9,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/1.00      | ~ l1_pre_topc(X1)
% 3.95/1.00      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_718,plain,
% 3.95/1.00      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
% 3.95/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.95/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2245,plain,
% 3.95/1.00      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
% 3.95/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_712,c_718]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_934,plain,
% 3.95/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.95/1.00      | ~ l1_pre_topc(sK0)
% 3.95/1.00      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2532,plain,
% 3.95/1.00      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 3.95/1.00      inference(global_propositional_subsumption,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_2245,c_16,c_15,c_934]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4855,plain,
% 3.95/1.00      ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 3.95/1.00      inference(demodulation,[status(thm)],[c_4852,c_2532]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_7,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.95/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_720,plain,
% 3.95/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.95/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_942,plain,
% 3.95/1.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_712,c_720]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/1.00      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_6,plain,
% 3.95/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.95/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_115,plain,
% 3.95/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.95/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_116,plain,
% 3.95/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.95/1.00      inference(renaming,[status(thm)],[c_115]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_140,plain,
% 3.95/1.00      ( ~ r1_tarski(X0,X1)
% 3.95/1.00      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.95/1.00      inference(bin_hyper_res,[status(thm)],[c_3,c_116]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_710,plain,
% 3.95/1.00      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 3.95/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_140]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2057,plain,
% 3.95/1.00      ( k9_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_942,c_710]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_5,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/1.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_142,plain,
% 3.95/1.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.95/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_116]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_708,plain,
% 3.95/1.00      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.95/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_142]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1155,plain,
% 3.95/1.00      ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_942,c_708]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_2059,plain,
% 3.95/1.00      ( k9_subset_1(u1_struct_0(sK0),sK1,X0) = k3_xboole_0(X0,sK1) ),
% 3.95/1.00      inference(light_normalisation,[status(thm)],[c_2057,c_1155]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4864,plain,
% 3.95/1.00      ( k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) = k2_tops_1(sK0,sK1) ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_4855,c_2059]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1,plain,
% 3.95/1.00      ( r1_tarski(X0,X0) ),
% 3.95/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_722,plain,
% 3.95/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1154,plain,
% 3.95/1.00      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_722,c_708]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_4,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.95/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_141,plain,
% 3.95/1.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 3.95/1.00      | ~ r1_tarski(X2,X0) ),
% 3.95/1.00      inference(bin_hyper_res,[status(thm)],[c_4,c_116]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_709,plain,
% 3.95/1.00      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 3.95/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_141]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1868,plain,
% 3.95/1.00      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
% 3.95/1.00      | r1_tarski(X1,X1) != iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_1154,c_709]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8606,plain,
% 3.95/1.00      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
% 3.95/1.00      inference(forward_subsumption_resolution,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_1868,c_722]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_8612,plain,
% 3.95/1.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.95/1.00      inference(superposition,[status(thm)],[c_4864,c_8606]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_316,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.95/1.00      theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_889,plain,
% 3.95/1.00      ( m1_subset_1(X0,X1)
% 3.95/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.95/1.00      | X0 != X2
% 3.95/1.00      | X1 != k1_zfmisc_1(X3) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_316]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1053,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/1.00      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.95/1.00      | X2 != X0
% 3.95/1.00      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_889]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1391,plain,
% 3.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/1.00      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 3.95/1.00      | k2_tops_1(sK0,sK1) != X0
% 3.95/1.00      | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(X1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_1053]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1725,plain,
% 3.95/1.00      ( ~ m1_subset_1(k2_tops_1(X0,sK1),k1_zfmisc_1(X1))
% 3.95/1.00      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 3.95/1.00      | k2_tops_1(sK0,sK1) != k2_tops_1(X0,sK1)
% 3.95/1.00      | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(X1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_1391]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_5534,plain,
% 3.95/1.00      ( ~ m1_subset_1(k2_tops_1(X0,sK1),k1_zfmisc_1(sK1))
% 3.95/1.00      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 3.95/1.00      | k2_tops_1(sK0,sK1) != k2_tops_1(X0,sK1)
% 3.95/1.00      | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(sK1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_1725]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_5535,plain,
% 3.95/1.00      ( k2_tops_1(sK0,sK1) != k2_tops_1(X0,sK1)
% 3.95/1.00      | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(sK1)
% 3.95/1.00      | m1_subset_1(k2_tops_1(X0,sK1),k1_zfmisc_1(sK1)) != iProver_top
% 3.95/1.00      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_5534]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_5537,plain,
% 3.95/1.00      ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
% 3.95/1.00      | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k1_zfmisc_1(sK1)
% 3.95/1.00      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = iProver_top
% 3.95/1.00      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) != iProver_top ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_5535]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_315,plain,
% 3.95/1.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.95/1.00      theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_1737,plain,
% 3.95/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0
% 3.95/1.00      | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k1_zfmisc_1(X0) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_315]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_3219,plain,
% 3.95/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != sK1
% 3.95/1.00      | k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k1_zfmisc_1(sK1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_1737]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_311,plain,( X0 = X0 ),theory(equality) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_988,plain,
% 3.95/1.00      ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_311]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_842,plain,
% 3.95/1.00      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 3.95/1.00      | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.95/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_843,plain,
% 3.95/1.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
% 3.95/1.00      | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_13,negated_conjecture,
% 3.95/1.00      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.95/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(c_20,plain,
% 3.95/1.00      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 3.95/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.95/1.00  
% 3.95/1.00  cnf(contradiction,plain,
% 3.95/1.00      ( $false ),
% 3.95/1.00      inference(minisat,
% 3.95/1.00                [status(thm)],
% 3.95/1.00                [c_8612,c_5537,c_3219,c_988,c_928,c_843,c_20,c_14,c_15,
% 3.95/1.00                 c_16]) ).
% 3.95/1.00  
% 3.95/1.00  
% 3.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/1.00  
% 3.95/1.00  ------                               Statistics
% 3.95/1.00  
% 3.95/1.00  ------ Selected
% 3.95/1.00  
% 3.95/1.00  total_time:                             0.31
% 3.95/1.00  
%------------------------------------------------------------------------------
