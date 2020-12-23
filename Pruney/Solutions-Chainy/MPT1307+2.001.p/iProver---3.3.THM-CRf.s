%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:34 EST 2020

% Result     : Theorem 15.15s
% Output     : CNFRefutation 15.15s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 144 expanded)
%              Number of clauses        :   44 (  51 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  196 ( 533 expanded)
%              Number of equality atoms :   57 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v2_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v2_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27,f26,f25])).

fof(f47,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v2_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_329,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_322,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4317,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_329,c_322])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_120,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_121,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_120])).

cnf(c_152,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_121])).

cnf(c_4615,plain,
    ( v2_tops_2(k7_subset_1(X0,X1,X2),X3)
    | ~ v2_tops_2(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X0) ),
    inference(resolution,[status(thm)],[c_4317,c_152])).

cnf(c_55071,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_14,c_4615])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_731,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2341,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_736])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_732,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2340,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_736])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_742,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3043,plain,
    ( k2_xboole_0(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2340,c_742])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_739,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14330,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3043,c_739])).

cnf(c_737,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_735,plain,
    ( v2_tops_2(X0,X1) != iProver_top
    | v2_tops_2(X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1206,plain,
    ( v2_tops_2(X0,sK0) = iProver_top
    | v2_tops_2(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_735])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,negated_conjecture,
    ( v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,plain,
    ( v2_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1773,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | v2_tops_2(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1206,c_19,c_22])).

cnf(c_1774,plain,
    ( v2_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1773])).

cnf(c_2614,plain,
    ( v2_tops_2(X0,sK0) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_1774])).

cnf(c_16918,plain,
    ( v2_tops_2(k4_xboole_0(X0,sK2),sK0) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14330,c_2614])).

cnf(c_29558,plain,
    ( v2_tops_2(k4_xboole_0(sK1,sK2),sK0) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2341,c_16918])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_740,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_31442,plain,
    ( v2_tops_2(k4_xboole_0(sK1,sK2),sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29558,c_740])).

cnf(c_31443,plain,
    ( v2_tops_2(k4_xboole_0(sK1,sK2),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_31442])).

cnf(c_902,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[status(thm)],[c_12,c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55071,c_31443,c_902])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:53:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.15/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.15/2.48  
% 15.15/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.15/2.48  
% 15.15/2.48  ------  iProver source info
% 15.15/2.48  
% 15.15/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.15/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.15/2.48  git: non_committed_changes: false
% 15.15/2.48  git: last_make_outside_of_git: false
% 15.15/2.48  
% 15.15/2.48  ------ 
% 15.15/2.48  ------ Parsing...
% 15.15/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.15/2.48  
% 15.15/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.15/2.48  
% 15.15/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.15/2.48  
% 15.15/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.15/2.48  ------ Proving...
% 15.15/2.48  ------ Problem Properties 
% 15.15/2.48  
% 15.15/2.48  
% 15.15/2.48  clauses                                 18
% 15.15/2.48  conjectures                             5
% 15.15/2.48  EPR                                     5
% 15.15/2.48  Horn                                    18
% 15.15/2.48  unary                                   10
% 15.15/2.48  binary                                  6
% 15.15/2.48  lits                                    31
% 15.15/2.48  lits eq                                 5
% 15.15/2.48  fd_pure                                 0
% 15.15/2.48  fd_pseudo                               0
% 15.15/2.48  fd_cond                                 0
% 15.15/2.48  fd_pseudo_cond                          1
% 15.15/2.48  AC symbols                              0
% 15.15/2.48  
% 15.15/2.48  ------ Input Options Time Limit: Unbounded
% 15.15/2.48  
% 15.15/2.48  
% 15.15/2.48  ------ 
% 15.15/2.48  Current options:
% 15.15/2.48  ------ 
% 15.15/2.48  
% 15.15/2.48  
% 15.15/2.48  
% 15.15/2.48  
% 15.15/2.48  ------ Proving...
% 15.15/2.48  
% 15.15/2.48  
% 15.15/2.48  % SZS status Theorem for theBenchmark.p
% 15.15/2.48  
% 15.15/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.15/2.48  
% 15.15/2.48  fof(f12,conjecture,(
% 15.15/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 15.15/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.15/2.48  
% 15.15/2.48  fof(f13,negated_conjecture,(
% 15.15/2.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 15.15/2.48    inference(negated_conjecture,[],[f12])).
% 15.15/2.48  
% 15.15/2.48  fof(f20,plain,(
% 15.15/2.48    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 15.15/2.48    inference(ennf_transformation,[],[f13])).
% 15.15/2.48  
% 15.15/2.48  fof(f21,plain,(
% 15.15/2.48    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 15.15/2.48    inference(flattening,[],[f20])).
% 15.15/2.48  
% 15.15/2.48  fof(f27,plain,(
% 15.15/2.48    ( ! [X0,X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v2_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 15.15/2.48    introduced(choice_axiom,[])).
% 15.15/2.48  
% 15.15/2.48  fof(f26,plain,(
% 15.15/2.48    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v2_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 15.15/2.48    introduced(choice_axiom,[])).
% 15.15/2.48  
% 15.15/2.48  fof(f25,plain,(
% 15.15/2.48    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 15.15/2.48    introduced(choice_axiom,[])).
% 15.15/2.48  
% 15.15/2.48  fof(f28,plain,(
% 15.15/2.48    ((~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 15.15/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27,f26,f25])).
% 15.15/2.48  
% 15.15/2.48  fof(f47,plain,(
% 15.15/2.48    ~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 15.15/2.48    inference(cnf_transformation,[],[f28])).
% 15.15/2.48  
% 15.15/2.48  fof(f9,axiom,(
% 15.15/2.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 15.15/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.15/2.48  
% 15.15/2.48  fof(f17,plain,(
% 15.15/2.48    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.15/2.48    inference(ennf_transformation,[],[f9])).
% 15.15/2.48  
% 15.15/2.48  fof(f39,plain,(
% 15.15/2.48    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.15/2.48    inference(cnf_transformation,[],[f17])).
% 15.15/2.48  
% 15.15/2.48  fof(f10,axiom,(
% 15.15/2.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.15/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.15/2.48  
% 15.15/2.48  fof(f24,plain,(
% 15.15/2.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.15/2.48    inference(nnf_transformation,[],[f10])).
% 15.15/2.48  
% 15.15/2.48  fof(f41,plain,(
% 15.15/2.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.15/2.48    inference(cnf_transformation,[],[f24])).
% 15.15/2.48  
% 15.15/2.48  fof(f44,plain,(
% 15.15/2.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 15.15/2.48    inference(cnf_transformation,[],[f28])).
% 15.15/2.48  
% 15.15/2.48  fof(f40,plain,(
% 15.15/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.15/2.48    inference(cnf_transformation,[],[f24])).
% 15.15/2.48  
% 15.15/2.48  fof(f45,plain,(
% 15.15/2.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 15.15/2.48    inference(cnf_transformation,[],[f28])).
% 15.15/2.48  
% 15.15/2.48  fof(f3,axiom,(
% 15.15/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.15/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.15/2.48  
% 15.15/2.48  fof(f14,plain,(
% 15.15/2.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.15/2.48    inference(ennf_transformation,[],[f3])).
% 15.15/2.48  
% 15.15/2.48  fof(f33,plain,(
% 15.15/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.15/2.48    inference(cnf_transformation,[],[f14])).
% 15.15/2.48  
% 15.15/2.48  fof(f7,axiom,(
% 15.15/2.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 15.15/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.15/2.48  
% 15.15/2.48  fof(f15,plain,(
% 15.15/2.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.15/2.48    inference(ennf_transformation,[],[f7])).
% 15.15/2.48  
% 15.15/2.48  fof(f37,plain,(
% 15.15/2.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 15.15/2.48    inference(cnf_transformation,[],[f15])).
% 15.15/2.48  
% 15.15/2.48  fof(f11,axiom,(
% 15.15/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 15.15/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.15/2.48  
% 15.15/2.48  fof(f18,plain,(
% 15.15/2.48    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 15.15/2.48    inference(ennf_transformation,[],[f11])).
% 15.15/2.48  
% 15.15/2.48  fof(f19,plain,(
% 15.15/2.48    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 15.15/2.48    inference(flattening,[],[f18])).
% 15.15/2.48  
% 15.15/2.48  fof(f42,plain,(
% 15.15/2.48    ( ! [X2,X0,X1] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 15.15/2.48    inference(cnf_transformation,[],[f19])).
% 15.15/2.48  
% 15.15/2.48  fof(f43,plain,(
% 15.15/2.48    l1_pre_topc(sK0)),
% 15.15/2.48    inference(cnf_transformation,[],[f28])).
% 15.15/2.48  
% 15.15/2.48  fof(f46,plain,(
% 15.15/2.48    v2_tops_2(sK1,sK0)),
% 15.15/2.48    inference(cnf_transformation,[],[f28])).
% 15.15/2.48  
% 15.15/2.48  fof(f5,axiom,(
% 15.15/2.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.15/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.15/2.48  
% 15.15/2.48  fof(f35,plain,(
% 15.15/2.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.15/2.48    inference(cnf_transformation,[],[f5])).
% 15.15/2.48  
% 15.15/2.48  cnf(c_14,negated_conjecture,
% 15.15/2.48      ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 15.15/2.48      inference(cnf_transformation,[],[f47]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_329,plain,
% 15.15/2.48      ( ~ v2_tops_2(X0,X1) | v2_tops_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.15/2.48      theory(equality) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_322,plain,( X0 = X0 ),theory(equality) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_4317,plain,
% 15.15/2.48      ( ~ v2_tops_2(X0,X1) | v2_tops_2(X2,X1) | X2 != X0 ),
% 15.15/2.48      inference(resolution,[status(thm)],[c_329,c_322]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_10,plain,
% 15.15/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.15/2.48      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 15.15/2.48      inference(cnf_transformation,[],[f39]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_11,plain,
% 15.15/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.15/2.48      inference(cnf_transformation,[],[f41]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_120,plain,
% 15.15/2.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.15/2.48      inference(prop_impl,[status(thm)],[c_11]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_121,plain,
% 15.15/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.15/2.48      inference(renaming,[status(thm)],[c_120]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_152,plain,
% 15.15/2.48      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 15.15/2.48      inference(bin_hyper_res,[status(thm)],[c_10,c_121]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_4615,plain,
% 15.15/2.48      ( v2_tops_2(k7_subset_1(X0,X1,X2),X3)
% 15.15/2.48      | ~ v2_tops_2(k4_xboole_0(X1,X2),X3)
% 15.15/2.48      | ~ r1_tarski(X1,X0) ),
% 15.15/2.48      inference(resolution,[status(thm)],[c_4317,c_152]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_55071,plain,
% 15.15/2.48      ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
% 15.15/2.48      | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.15/2.48      inference(resolution,[status(thm)],[c_14,c_4615]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_17,negated_conjecture,
% 15.15/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 15.15/2.48      inference(cnf_transformation,[],[f44]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_731,plain,
% 15.15/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_12,plain,
% 15.15/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.15/2.48      inference(cnf_transformation,[],[f40]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_736,plain,
% 15.15/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.15/2.48      | r1_tarski(X0,X1) = iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_2341,plain,
% 15.15/2.48      ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.15/2.48      inference(superposition,[status(thm)],[c_731,c_736]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_16,negated_conjecture,
% 15.15/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 15.15/2.48      inference(cnf_transformation,[],[f45]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_732,plain,
% 15.15/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_2340,plain,
% 15.15/2.48      ( r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.15/2.48      inference(superposition,[status(thm)],[c_732,c_736]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_4,plain,
% 15.15/2.48      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.15/2.48      inference(cnf_transformation,[],[f33]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_742,plain,
% 15.15/2.48      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_3043,plain,
% 15.15/2.48      ( k2_xboole_0(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 15.15/2.48      inference(superposition,[status(thm)],[c_2340,c_742]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_8,plain,
% 15.15/2.48      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 15.15/2.48      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 15.15/2.48      inference(cnf_transformation,[],[f37]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_739,plain,
% 15.15/2.48      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 15.15/2.48      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_14330,plain,
% 15.15/2.48      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.15/2.48      | r1_tarski(k4_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.15/2.48      inference(superposition,[status(thm)],[c_3043,c_739]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_737,plain,
% 15.15/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.15/2.48      | r1_tarski(X0,X1) != iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_13,plain,
% 15.15/2.48      ( ~ v2_tops_2(X0,X1)
% 15.15/2.48      | v2_tops_2(X2,X1)
% 15.15/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 15.15/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 15.15/2.48      | ~ r1_tarski(X2,X0)
% 15.15/2.48      | ~ l1_pre_topc(X1) ),
% 15.15/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_735,plain,
% 15.15/2.48      ( v2_tops_2(X0,X1) != iProver_top
% 15.15/2.48      | v2_tops_2(X2,X1) = iProver_top
% 15.15/2.48      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 15.15/2.48      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 15.15/2.48      | r1_tarski(X2,X0) != iProver_top
% 15.15/2.48      | l1_pre_topc(X1) != iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_1206,plain,
% 15.15/2.48      ( v2_tops_2(X0,sK0) = iProver_top
% 15.15/2.48      | v2_tops_2(sK1,sK0) != iProver_top
% 15.15/2.48      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 15.15/2.48      | r1_tarski(X0,sK1) != iProver_top
% 15.15/2.48      | l1_pre_topc(sK0) != iProver_top ),
% 15.15/2.48      inference(superposition,[status(thm)],[c_731,c_735]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_18,negated_conjecture,
% 15.15/2.48      ( l1_pre_topc(sK0) ),
% 15.15/2.48      inference(cnf_transformation,[],[f43]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_19,plain,
% 15.15/2.48      ( l1_pre_topc(sK0) = iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_15,negated_conjecture,
% 15.15/2.48      ( v2_tops_2(sK1,sK0) ),
% 15.15/2.48      inference(cnf_transformation,[],[f46]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_22,plain,
% 15.15/2.48      ( v2_tops_2(sK1,sK0) = iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_1773,plain,
% 15.15/2.48      ( r1_tarski(X0,sK1) != iProver_top
% 15.15/2.48      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 15.15/2.48      | v2_tops_2(X0,sK0) = iProver_top ),
% 15.15/2.48      inference(global_propositional_subsumption,
% 15.15/2.48                [status(thm)],
% 15.15/2.48                [c_1206,c_19,c_22]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_1774,plain,
% 15.15/2.48      ( v2_tops_2(X0,sK0) = iProver_top
% 15.15/2.48      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 15.15/2.48      | r1_tarski(X0,sK1) != iProver_top ),
% 15.15/2.48      inference(renaming,[status(thm)],[c_1773]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_2614,plain,
% 15.15/2.48      ( v2_tops_2(X0,sK0) = iProver_top
% 15.15/2.48      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.15/2.48      | r1_tarski(X0,sK1) != iProver_top ),
% 15.15/2.48      inference(superposition,[status(thm)],[c_737,c_1774]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_16918,plain,
% 15.15/2.48      ( v2_tops_2(k4_xboole_0(X0,sK2),sK0) = iProver_top
% 15.15/2.48      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.15/2.48      | r1_tarski(k4_xboole_0(X0,sK2),sK1) != iProver_top ),
% 15.15/2.48      inference(superposition,[status(thm)],[c_14330,c_2614]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_29558,plain,
% 15.15/2.48      ( v2_tops_2(k4_xboole_0(sK1,sK2),sK0) = iProver_top
% 15.15/2.48      | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top ),
% 15.15/2.48      inference(superposition,[status(thm)],[c_2341,c_16918]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_6,plain,
% 15.15/2.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.15/2.48      inference(cnf_transformation,[],[f35]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_740,plain,
% 15.15/2.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 15.15/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_31442,plain,
% 15.15/2.48      ( v2_tops_2(k4_xboole_0(sK1,sK2),sK0) = iProver_top ),
% 15.15/2.48      inference(forward_subsumption_resolution,
% 15.15/2.48                [status(thm)],
% 15.15/2.48                [c_29558,c_740]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_31443,plain,
% 15.15/2.48      ( v2_tops_2(k4_xboole_0(sK1,sK2),sK0) ),
% 15.15/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_31442]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(c_902,plain,
% 15.15/2.48      ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.15/2.48      inference(resolution,[status(thm)],[c_12,c_17]) ).
% 15.15/2.48  
% 15.15/2.48  cnf(contradiction,plain,
% 15.15/2.48      ( $false ),
% 15.15/2.48      inference(minisat,[status(thm)],[c_55071,c_31443,c_902]) ).
% 15.15/2.48  
% 15.15/2.48  
% 15.15/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.15/2.48  
% 15.15/2.48  ------                               Statistics
% 15.15/2.48  
% 15.15/2.48  ------ Selected
% 15.15/2.48  
% 15.15/2.48  total_time:                             1.713
% 15.15/2.48  
%------------------------------------------------------------------------------
