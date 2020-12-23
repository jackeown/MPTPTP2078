%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:14 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 434 expanded)
%              Number of clauses        :   61 ( 151 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  243 (1447 expanded)
%              Number of equality atoms :  104 ( 255 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK1,k2_tops_1(X0,sK1))
          | ~ v2_tops_1(sK1,X0) )
        & ( r1_tarski(sK1,k2_tops_1(X0,sK1))
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f54,f45,f45])).

fof(f69,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f53,f45])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f45])).

fof(f70,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_776,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_781,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15742,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_781])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3328,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_783])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_198,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_154])).

cnf(c_772,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_3871,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_3328,c_772])).

cnf(c_15745,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15742,c_3871])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16965,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15745,c_26])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_16976,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_16965,c_0])).

cnf(c_23,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_777,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_786,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_787,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4221,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_787])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4229,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4221,c_4])).

cnf(c_4841,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_4229])).

cnf(c_16968,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16965,c_4841])).

cnf(c_27,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2005,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2006,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2005])).

cnf(c_17038,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16968,c_26,c_27,c_2006])).

cnf(c_21,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_779,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15926,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_779])).

cnf(c_16351,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15926,c_26])).

cnf(c_16352,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16351])).

cnf(c_17043,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17038,c_16352])).

cnf(c_17260,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_16976,c_17043])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_790,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2239,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_790,c_787])).

cnf(c_11,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1410,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_11,c_15])).

cnf(c_2036,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1410,c_15])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2046,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2036,c_7])).

cnf(c_2435,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_2239,c_2046])).

cnf(c_2442,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2239,c_2036])).

cnf(c_17261,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_17260,c_2435,c_2442])).

cnf(c_2044,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2036,c_790])).

cnf(c_17273,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17261,c_2044])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17273,c_17038,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.72/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/1.00  
% 3.72/1.00  ------  iProver source info
% 3.72/1.00  
% 3.72/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.72/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/1.00  git: non_committed_changes: false
% 3.72/1.00  git: last_make_outside_of_git: false
% 3.72/1.00  
% 3.72/1.00  ------ 
% 3.72/1.00  ------ Parsing...
% 3.72/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/1.00  ------ Proving...
% 3.72/1.00  ------ Problem Properties 
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  clauses                                 26
% 3.72/1.00  conjectures                             4
% 3.72/1.00  EPR                                     3
% 3.72/1.00  Horn                                    25
% 3.72/1.00  unary                                   10
% 3.72/1.00  binary                                  11
% 3.72/1.00  lits                                    49
% 3.72/1.00  lits eq                                 14
% 3.72/1.00  fd_pure                                 0
% 3.72/1.00  fd_pseudo                               0
% 3.72/1.00  fd_cond                                 2
% 3.72/1.00  fd_pseudo_cond                          0
% 3.72/1.00  AC symbols                              0
% 3.72/1.00  
% 3.72/1.00  ------ Input Options Time Limit: Unbounded
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  ------ 
% 3.72/1.00  Current options:
% 3.72/1.00  ------ 
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  ------ Proving...
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  % SZS status Theorem for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  fof(f22,conjecture,(
% 3.72/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f23,negated_conjecture,(
% 3.72/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.72/1.00    inference(negated_conjecture,[],[f22])).
% 3.72/1.00  
% 3.72/1.00  fof(f36,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f23])).
% 3.72/1.00  
% 3.72/1.00  fof(f39,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.72/1.00    inference(nnf_transformation,[],[f36])).
% 3.72/1.00  
% 3.72/1.00  fof(f40,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.72/1.00    inference(flattening,[],[f39])).
% 3.72/1.00  
% 3.72/1.00  fof(f42,plain,(
% 3.72/1.00    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f41,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f43,plain,(
% 3.72/1.00    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 3.72/1.00  
% 3.72/1.00  fof(f68,plain,(
% 3.72/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f20,axiom,(
% 3.72/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f34,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f20])).
% 3.72/1.00  
% 3.72/1.00  fof(f64,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f34])).
% 3.72/1.00  
% 3.72/1.00  fof(f18,axiom,(
% 3.72/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f37,plain,(
% 3.72/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.72/1.00    inference(nnf_transformation,[],[f18])).
% 3.72/1.00  
% 3.72/1.00  fof(f61,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f37])).
% 3.72/1.00  
% 3.72/1.00  fof(f16,axiom,(
% 3.72/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f32,plain,(
% 3.72/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/1.00    inference(ennf_transformation,[],[f16])).
% 3.72/1.00  
% 3.72/1.00  fof(f59,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f32])).
% 3.72/1.00  
% 3.72/1.00  fof(f2,axiom,(
% 3.72/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f45,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f2])).
% 3.72/1.00  
% 3.72/1.00  fof(f76,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/1.00    inference(definition_unfolding,[],[f59,f45])).
% 3.72/1.00  
% 3.72/1.00  fof(f62,plain,(
% 3.72/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f37])).
% 3.72/1.00  
% 3.72/1.00  fof(f67,plain,(
% 3.72/1.00    l1_pre_topc(sK0)),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f11,axiom,(
% 3.72/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f54,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f11])).
% 3.72/1.00  
% 3.72/1.00  fof(f71,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.72/1.00    inference(definition_unfolding,[],[f54,f45,f45])).
% 3.72/1.00  
% 3.72/1.00  fof(f69,plain,(
% 3.72/1.00    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f10,axiom,(
% 3.72/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f29,plain,(
% 3.72/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.72/1.00    inference(ennf_transformation,[],[f10])).
% 3.72/1.00  
% 3.72/1.00  fof(f53,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f29])).
% 3.72/1.00  
% 3.72/1.00  fof(f74,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.72/1.00    inference(definition_unfolding,[],[f53,f45])).
% 3.72/1.00  
% 3.72/1.00  fof(f9,axiom,(
% 3.72/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f28,plain,(
% 3.72/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.72/1.00    inference(ennf_transformation,[],[f9])).
% 3.72/1.00  
% 3.72/1.00  fof(f52,plain,(
% 3.72/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f28])).
% 3.72/1.00  
% 3.72/1.00  fof(f5,axiom,(
% 3.72/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f48,plain,(
% 3.72/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.72/1.00    inference(cnf_transformation,[],[f5])).
% 3.72/1.00  
% 3.72/1.00  fof(f21,axiom,(
% 3.72/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f35,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f21])).
% 3.72/1.00  
% 3.72/1.00  fof(f38,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.72/1.00    inference(nnf_transformation,[],[f35])).
% 3.72/1.00  
% 3.72/1.00  fof(f66,plain,(
% 3.72/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f38])).
% 3.72/1.00  
% 3.72/1.00  fof(f65,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f38])).
% 3.72/1.00  
% 3.72/1.00  fof(f4,axiom,(
% 3.72/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f47,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f4])).
% 3.72/1.00  
% 3.72/1.00  fof(f13,axiom,(
% 3.72/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f56,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f13])).
% 3.72/1.00  
% 3.72/1.00  fof(f17,axiom,(
% 3.72/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f60,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f17])).
% 3.72/1.00  
% 3.72/1.00  fof(f8,axiom,(
% 3.72/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.72/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f51,plain,(
% 3.72/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.72/1.00    inference(cnf_transformation,[],[f8])).
% 3.72/1.00  
% 3.72/1.00  fof(f73,plain,(
% 3.72/1.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.72/1.00    inference(definition_unfolding,[],[f51,f45])).
% 3.72/1.00  
% 3.72/1.00  fof(f70,plain,(
% 3.72/1.00    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  cnf(c_24,negated_conjecture,
% 3.72/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.72/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_776,plain,
% 3.72/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_19,plain,
% 3.72/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/1.00      | ~ l1_pre_topc(X1)
% 3.72/1.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_781,plain,
% 3.72/1.00      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 3.72/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.72/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_15742,plain,
% 3.72/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.72/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_776,c_781]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_17,plain,
% 3.72/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_783,plain,
% 3.72/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.72/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3328,plain,
% 3.72/1.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_776,c_783]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_14,plain,
% 3.72/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 3.72/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_16,plain,
% 3.72/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_153,plain,
% 3.72/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.72/1.00      inference(prop_impl,[status(thm)],[c_16]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_154,plain,
% 3.72/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.72/1.00      inference(renaming,[status(thm)],[c_153]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_198,plain,
% 3.72/1.00      ( ~ r1_tarski(X0,X1)
% 3.72/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 3.72/1.00      inference(bin_hyper_res,[status(thm)],[c_14,c_154]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_772,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 3.72/1.00      | r1_tarski(X0,X2) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3871,plain,
% 3.72/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_3328,c_772]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_15745,plain,
% 3.72/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1)
% 3.72/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.72/1.00      inference(demodulation,[status(thm)],[c_15742,c_3871]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_25,negated_conjecture,
% 3.72/1.00      ( l1_pre_topc(sK0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_26,plain,
% 3.72/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_16965,plain,
% 3.72/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_15745,c_26]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_0,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_16976,plain,
% 3.72/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_16965,c_0]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_23,negated_conjecture,
% 3.72/1.00      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.72/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_777,plain,
% 3.72/1.00      ( v2_tops_1(sK1,sK0) = iProver_top
% 3.72/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_9,plain,
% 3.72/1.00      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 3.72/1.00      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 3.72/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_786,plain,
% 3.72/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 3.72/1.00      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_8,plain,
% 3.72/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_787,plain,
% 3.72/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_4221,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.72/1.00      | r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_786,c_787]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_4,plain,
% 3.72/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_4229,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.72/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.72/1.00      inference(demodulation,[status(thm)],[c_4221,c_4]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_4841,plain,
% 3.72/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_xboole_0
% 3.72/1.00      | v2_tops_1(sK1,sK0) = iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_777,c_4229]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_16968,plain,
% 3.72/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.72/1.00      | v2_tops_1(sK1,sK0) = iProver_top ),
% 3.72/1.00      inference(demodulation,[status(thm)],[c_16965,c_4841]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_27,plain,
% 3.72/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_20,plain,
% 3.72/1.00      ( v2_tops_1(X0,X1)
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/1.00      | ~ l1_pre_topc(X1)
% 3.72/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2005,plain,
% 3.72/1.00      ( v2_tops_1(sK1,sK0)
% 3.72/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.72/1.00      | ~ l1_pre_topc(sK0)
% 3.72/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2006,plain,
% 3.72/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.72/1.00      | v2_tops_1(sK1,sK0) = iProver_top
% 3.72/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.72/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_2005]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_17038,plain,
% 3.72/1.00      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_16968,c_26,c_27,c_2006]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_21,plain,
% 3.72/1.00      ( ~ v2_tops_1(X0,X1)
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/1.00      | ~ l1_pre_topc(X1)
% 3.72/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_779,plain,
% 3.72/1.00      ( k1_tops_1(X0,X1) = k1_xboole_0
% 3.72/1.00      | v2_tops_1(X1,X0) != iProver_top
% 3.72/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.72/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_15926,plain,
% 3.72/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.72/1.00      | v2_tops_1(sK1,sK0) != iProver_top
% 3.72/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_776,c_779]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_16351,plain,
% 3.72/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.72/1.00      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_15926,c_26]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_16352,plain,
% 3.72/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.72/1.00      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.72/1.00      inference(renaming,[status(thm)],[c_16351]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_17043,plain,
% 3.72/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_17038,c_16352]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_17260,plain,
% 3.72/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.72/1.00      inference(light_normalisation,[status(thm)],[c_16976,c_17043]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3,plain,
% 3.72/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_790,plain,
% 3.72/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2239,plain,
% 3.72/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_790,c_787]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_11,plain,
% 3.72/1.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_15,plain,
% 3.72/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1410,plain,
% 3.72/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_11,c_15]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2036,plain,
% 3.72/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_1410,c_15]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_7,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2046,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_2036,c_7]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2435,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.72/1.00      inference(demodulation,[status(thm)],[c_2239,c_2046]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2442,plain,
% 3.72/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_2239,c_2036]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_17261,plain,
% 3.72/1.00      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 3.72/1.00      inference(demodulation,[status(thm)],[c_17260,c_2435,c_2442]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2044,plain,
% 3.72/1.00      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_2036,c_790]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_17273,plain,
% 3.72/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_17261,c_2044]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_22,negated_conjecture,
% 3.72/1.00      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.72/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_29,plain,
% 3.72/1.00      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.72/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(contradiction,plain,
% 3.72/1.00      ( $false ),
% 3.72/1.00      inference(minisat,[status(thm)],[c_17273,c_17038,c_29]) ).
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  ------                               Statistics
% 3.72/1.00  
% 3.72/1.00  ------ Selected
% 3.72/1.00  
% 3.72/1.00  total_time:                             0.472
% 3.72/1.00  
%------------------------------------------------------------------------------
