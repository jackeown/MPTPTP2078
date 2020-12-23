%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:49 EST 2020

% Result     : CounterSatisfiable 2.17s
% Output     : Saturation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 346 expanded)
%              Number of clauses        :   41 ( 110 expanded)
%              Number of leaves         :   14 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  182 ( 863 expanded)
%              Number of equality atoms :  118 ( 580 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f39])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k2_struct_0(X0) = sK1
            & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) )
          | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)
            & k2_struct_0(X0) != sK1 ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k2_struct_0(sK0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)
              & k2_struct_0(sK0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19,f18])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f24,f39])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_145,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_338,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_591,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_590,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_588,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_599,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_588,c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_587,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1010,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_599,c_587])).

cnf(c_1395,plain,
    ( k7_subset_1(X0,X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_590,c_1010])).

cnf(c_1401,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_591,c_1395])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_586,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_835,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_586,c_587])).

cnf(c_1216,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1010,c_835])).

cnf(c_5,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1061,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_5,c_835])).

cnf(c_1242,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1216,c_1061])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_589,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1063,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) != k1_xboole_0
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_589])).

cnf(c_1241,plain,
    ( k7_subset_1(sK1,sK1,X0) != k1_xboole_0
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1216,c_1063])).

cnf(c_1233,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_1010])).

cnf(c_1215,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1010,c_587])).

cnf(c_1214,plain,
    ( k7_subset_1(X0,X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1010,c_589])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_156,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_155])).

cnf(c_585,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_1011,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_599,c_585])).

cnf(c_10,negated_conjecture,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_687,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_586,c_585])).

cnf(c_778,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_10,c_687])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_592,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 17:31:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.17/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.98  
% 2.17/0.98  ------  iProver source info
% 2.17/0.98  
% 2.17/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.98  git: non_committed_changes: false
% 2.17/0.98  git: last_make_outside_of_git: false
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options
% 2.17/0.98  
% 2.17/0.98  --out_options                           all
% 2.17/0.98  --tptp_safe_out                         true
% 2.17/0.98  --problem_path                          ""
% 2.17/0.98  --include_path                          ""
% 2.17/0.98  --clausifier                            res/vclausify_rel
% 2.17/0.98  --clausifier_options                    --mode clausify
% 2.17/0.98  --stdin                                 false
% 2.17/0.98  --stats_out                             all
% 2.17/0.98  
% 2.17/0.98  ------ General Options
% 2.17/0.98  
% 2.17/0.98  --fof                                   false
% 2.17/0.98  --time_out_real                         305.
% 2.17/0.98  --time_out_virtual                      -1.
% 2.17/0.98  --symbol_type_check                     false
% 2.17/0.98  --clausify_out                          false
% 2.17/0.98  --sig_cnt_out                           false
% 2.17/0.98  --trig_cnt_out                          false
% 2.17/0.98  --trig_cnt_out_tolerance                1.
% 2.17/0.98  --trig_cnt_out_sk_spl                   false
% 2.17/0.98  --abstr_cl_out                          false
% 2.17/0.98  
% 2.17/0.98  ------ Global Options
% 2.17/0.98  
% 2.17/0.98  --schedule                              default
% 2.17/0.98  --add_important_lit                     false
% 2.17/0.98  --prop_solver_per_cl                    1000
% 2.17/0.98  --min_unsat_core                        false
% 2.17/0.98  --soft_assumptions                      false
% 2.17/0.98  --soft_lemma_size                       3
% 2.17/0.98  --prop_impl_unit_size                   0
% 2.17/0.98  --prop_impl_unit                        []
% 2.17/0.98  --share_sel_clauses                     true
% 2.17/0.98  --reset_solvers                         false
% 2.17/0.98  --bc_imp_inh                            [conj_cone]
% 2.17/0.98  --conj_cone_tolerance                   3.
% 2.17/0.98  --extra_neg_conj                        none
% 2.17/0.98  --large_theory_mode                     true
% 2.17/0.98  --prolific_symb_bound                   200
% 2.17/0.98  --lt_threshold                          2000
% 2.17/0.98  --clause_weak_htbl                      true
% 2.17/0.98  --gc_record_bc_elim                     false
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing Options
% 2.17/0.98  
% 2.17/0.98  --preprocessing_flag                    true
% 2.17/0.98  --time_out_prep_mult                    0.1
% 2.17/0.98  --splitting_mode                        input
% 2.17/0.98  --splitting_grd                         true
% 2.17/0.98  --splitting_cvd                         false
% 2.17/0.98  --splitting_cvd_svl                     false
% 2.17/0.98  --splitting_nvd                         32
% 2.17/0.98  --sub_typing                            true
% 2.17/0.98  --prep_gs_sim                           true
% 2.17/0.98  --prep_unflatten                        true
% 2.17/0.98  --prep_res_sim                          true
% 2.17/0.98  --prep_upred                            true
% 2.17/0.98  --prep_sem_filter                       exhaustive
% 2.17/0.98  --prep_sem_filter_out                   false
% 2.17/0.98  --pred_elim                             true
% 2.17/0.98  --res_sim_input                         true
% 2.17/0.98  --eq_ax_congr_red                       true
% 2.17/0.98  --pure_diseq_elim                       true
% 2.17/0.98  --brand_transform                       false
% 2.17/0.98  --non_eq_to_eq                          false
% 2.17/0.98  --prep_def_merge                        true
% 2.17/0.98  --prep_def_merge_prop_impl              false
% 2.17/0.98  --prep_def_merge_mbd                    true
% 2.17/0.98  --prep_def_merge_tr_red                 false
% 2.17/0.98  --prep_def_merge_tr_cl                  false
% 2.17/0.98  --smt_preprocessing                     true
% 2.17/0.98  --smt_ac_axioms                         fast
% 2.17/0.98  --preprocessed_out                      false
% 2.17/0.98  --preprocessed_stats                    false
% 2.17/0.98  
% 2.17/0.98  ------ Abstraction refinement Options
% 2.17/0.98  
% 2.17/0.98  --abstr_ref                             []
% 2.17/0.98  --abstr_ref_prep                        false
% 2.17/0.98  --abstr_ref_until_sat                   false
% 2.17/0.98  --abstr_ref_sig_restrict                funpre
% 2.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.98  --abstr_ref_under                       []
% 2.17/0.98  
% 2.17/0.98  ------ SAT Options
% 2.17/0.98  
% 2.17/0.98  --sat_mode                              false
% 2.17/0.98  --sat_fm_restart_options                ""
% 2.17/0.98  --sat_gr_def                            false
% 2.17/0.98  --sat_epr_types                         true
% 2.17/0.98  --sat_non_cyclic_types                  false
% 2.17/0.98  --sat_finite_models                     false
% 2.17/0.98  --sat_fm_lemmas                         false
% 2.17/0.98  --sat_fm_prep                           false
% 2.17/0.98  --sat_fm_uc_incr                        true
% 2.17/0.98  --sat_out_model                         small
% 2.17/0.98  --sat_out_clauses                       false
% 2.17/0.98  
% 2.17/0.98  ------ QBF Options
% 2.17/0.98  
% 2.17/0.98  --qbf_mode                              false
% 2.17/0.98  --qbf_elim_univ                         false
% 2.17/0.98  --qbf_dom_inst                          none
% 2.17/0.98  --qbf_dom_pre_inst                      false
% 2.17/0.98  --qbf_sk_in                             false
% 2.17/0.98  --qbf_pred_elim                         true
% 2.17/0.98  --qbf_split                             512
% 2.17/0.98  
% 2.17/0.98  ------ BMC1 Options
% 2.17/0.98  
% 2.17/0.98  --bmc1_incremental                      false
% 2.17/0.98  --bmc1_axioms                           reachable_all
% 2.17/0.98  --bmc1_min_bound                        0
% 2.17/0.98  --bmc1_max_bound                        -1
% 2.17/0.98  --bmc1_max_bound_default                -1
% 2.17/0.98  --bmc1_symbol_reachability              true
% 2.17/0.98  --bmc1_property_lemmas                  false
% 2.17/0.98  --bmc1_k_induction                      false
% 2.17/0.98  --bmc1_non_equiv_states                 false
% 2.17/0.98  --bmc1_deadlock                         false
% 2.17/0.98  --bmc1_ucm                              false
% 2.17/0.98  --bmc1_add_unsat_core                   none
% 2.17/0.98  --bmc1_unsat_core_children              false
% 2.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.98  --bmc1_out_stat                         full
% 2.17/0.98  --bmc1_ground_init                      false
% 2.17/0.98  --bmc1_pre_inst_next_state              false
% 2.17/0.98  --bmc1_pre_inst_state                   false
% 2.17/0.98  --bmc1_pre_inst_reach_state             false
% 2.17/0.98  --bmc1_out_unsat_core                   false
% 2.17/0.98  --bmc1_aig_witness_out                  false
% 2.17/0.98  --bmc1_verbose                          false
% 2.17/0.98  --bmc1_dump_clauses_tptp                false
% 2.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.98  --bmc1_dump_file                        -
% 2.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.98  --bmc1_ucm_extend_mode                  1
% 2.17/0.98  --bmc1_ucm_init_mode                    2
% 2.17/0.98  --bmc1_ucm_cone_mode                    none
% 2.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.98  --bmc1_ucm_relax_model                  4
% 2.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.98  --bmc1_ucm_layered_model                none
% 2.17/0.98  --bmc1_ucm_max_lemma_size               10
% 2.17/0.98  
% 2.17/0.98  ------ AIG Options
% 2.17/0.98  
% 2.17/0.98  --aig_mode                              false
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation Options
% 2.17/0.98  
% 2.17/0.98  --instantiation_flag                    true
% 2.17/0.98  --inst_sos_flag                         false
% 2.17/0.98  --inst_sos_phase                        true
% 2.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel_side                     num_symb
% 2.17/0.98  --inst_solver_per_active                1400
% 2.17/0.98  --inst_solver_calls_frac                1.
% 2.17/0.98  --inst_passive_queue_type               priority_queues
% 2.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.98  --inst_passive_queues_freq              [25;2]
% 2.17/0.98  --inst_dismatching                      true
% 2.17/0.98  --inst_eager_unprocessed_to_passive     true
% 2.17/0.98  --inst_prop_sim_given                   true
% 2.17/0.98  --inst_prop_sim_new                     false
% 2.17/0.98  --inst_subs_new                         false
% 2.17/0.98  --inst_eq_res_simp                      false
% 2.17/0.98  --inst_subs_given                       false
% 2.17/0.98  --inst_orphan_elimination               true
% 2.17/0.98  --inst_learning_loop_flag               true
% 2.17/0.98  --inst_learning_start                   3000
% 2.17/0.98  --inst_learning_factor                  2
% 2.17/0.98  --inst_start_prop_sim_after_learn       3
% 2.17/0.98  --inst_sel_renew                        solver
% 2.17/0.98  --inst_lit_activity_flag                true
% 2.17/0.98  --inst_restr_to_given                   false
% 2.17/0.98  --inst_activity_threshold               500
% 2.17/0.98  --inst_out_proof                        true
% 2.17/0.98  
% 2.17/0.98  ------ Resolution Options
% 2.17/0.98  
% 2.17/0.98  --resolution_flag                       true
% 2.17/0.98  --res_lit_sel                           adaptive
% 2.17/0.98  --res_lit_sel_side                      none
% 2.17/0.98  --res_ordering                          kbo
% 2.17/0.98  --res_to_prop_solver                    active
% 2.17/0.98  --res_prop_simpl_new                    false
% 2.17/0.98  --res_prop_simpl_given                  true
% 2.17/0.98  --res_passive_queue_type                priority_queues
% 2.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.98  --res_passive_queues_freq               [15;5]
% 2.17/0.98  --res_forward_subs                      full
% 2.17/0.98  --res_backward_subs                     full
% 2.17/0.98  --res_forward_subs_resolution           true
% 2.17/0.98  --res_backward_subs_resolution          true
% 2.17/0.98  --res_orphan_elimination                true
% 2.17/0.98  --res_time_limit                        2.
% 2.17/0.98  --res_out_proof                         true
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Options
% 2.17/0.98  
% 2.17/0.98  --superposition_flag                    true
% 2.17/0.98  --sup_passive_queue_type                priority_queues
% 2.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.98  --demod_completeness_check              fast
% 2.17/0.98  --demod_use_ground                      true
% 2.17/0.98  --sup_to_prop_solver                    passive
% 2.17/0.98  --sup_prop_simpl_new                    true
% 2.17/0.98  --sup_prop_simpl_given                  true
% 2.17/0.98  --sup_fun_splitting                     false
% 2.17/0.98  --sup_smt_interval                      50000
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Simplification Setup
% 2.17/0.98  
% 2.17/0.98  --sup_indices_passive                   []
% 2.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_full_bw                           [BwDemod]
% 2.17/0.98  --sup_immed_triv                        [TrivRules]
% 2.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_immed_bw_main                     []
% 2.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  
% 2.17/0.98  ------ Combination Options
% 2.17/0.98  
% 2.17/0.98  --comb_res_mult                         3
% 2.17/0.98  --comb_sup_mult                         2
% 2.17/0.98  --comb_inst_mult                        10
% 2.17/0.98  
% 2.17/0.98  ------ Debug Options
% 2.17/0.98  
% 2.17/0.98  --dbg_backtrace                         false
% 2.17/0.98  --dbg_dump_prop_clauses                 false
% 2.17/0.98  --dbg_dump_prop_clauses_file            -
% 2.17/0.98  --dbg_out_stat                          false
% 2.17/0.98  ------ Parsing...
% 2.17/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.98  ------ Proving...
% 2.17/0.98  ------ Problem Properties 
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  clauses                                 12
% 2.17/0.98  conjectures                             3
% 2.17/0.98  EPR                                     2
% 2.17/0.98  Horn                                    11
% 2.17/0.98  unary                                   5
% 2.17/0.98  binary                                  6
% 2.17/0.98  lits                                    20
% 2.17/0.98  lits eq                                 11
% 2.17/0.98  fd_pure                                 0
% 2.17/0.98  fd_pseudo                               0
% 2.17/0.98  fd_cond                                 0
% 2.17/0.98  fd_pseudo_cond                          1
% 2.17/0.98  AC symbols                              0
% 2.17/0.98  
% 2.17/0.98  ------ Schedule dynamic 5 is on 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  Current options:
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  ------ Input Options
% 2.17/0.98  
% 2.17/0.98  --out_options                           all
% 2.17/0.98  --tptp_safe_out                         true
% 2.17/0.98  --problem_path                          ""
% 2.17/0.98  --include_path                          ""
% 2.17/0.98  --clausifier                            res/vclausify_rel
% 2.17/0.98  --clausifier_options                    --mode clausify
% 2.17/0.98  --stdin                                 false
% 2.17/0.98  --stats_out                             all
% 2.17/0.98  
% 2.17/0.98  ------ General Options
% 2.17/0.98  
% 2.17/0.98  --fof                                   false
% 2.17/0.98  --time_out_real                         305.
% 2.17/0.98  --time_out_virtual                      -1.
% 2.17/0.98  --symbol_type_check                     false
% 2.17/0.98  --clausify_out                          false
% 2.17/0.98  --sig_cnt_out                           false
% 2.17/0.98  --trig_cnt_out                          false
% 2.17/0.98  --trig_cnt_out_tolerance                1.
% 2.17/0.98  --trig_cnt_out_sk_spl                   false
% 2.17/0.98  --abstr_cl_out                          false
% 2.17/0.98  
% 2.17/0.98  ------ Global Options
% 2.17/0.98  
% 2.17/0.98  --schedule                              default
% 2.17/0.98  --add_important_lit                     false
% 2.17/0.98  --prop_solver_per_cl                    1000
% 2.17/0.98  --min_unsat_core                        false
% 2.17/0.98  --soft_assumptions                      false
% 2.17/0.98  --soft_lemma_size                       3
% 2.17/0.98  --prop_impl_unit_size                   0
% 2.17/0.98  --prop_impl_unit                        []
% 2.17/0.98  --share_sel_clauses                     true
% 2.17/0.98  --reset_solvers                         false
% 2.17/0.98  --bc_imp_inh                            [conj_cone]
% 2.17/0.98  --conj_cone_tolerance                   3.
% 2.17/0.98  --extra_neg_conj                        none
% 2.17/0.98  --large_theory_mode                     true
% 2.17/0.98  --prolific_symb_bound                   200
% 2.17/0.98  --lt_threshold                          2000
% 2.17/0.98  --clause_weak_htbl                      true
% 2.17/0.98  --gc_record_bc_elim                     false
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing Options
% 2.17/0.98  
% 2.17/0.98  --preprocessing_flag                    true
% 2.17/0.98  --time_out_prep_mult                    0.1
% 2.17/0.98  --splitting_mode                        input
% 2.17/0.98  --splitting_grd                         true
% 2.17/0.98  --splitting_cvd                         false
% 2.17/0.98  --splitting_cvd_svl                     false
% 2.17/0.98  --splitting_nvd                         32
% 2.17/0.98  --sub_typing                            true
% 2.17/0.98  --prep_gs_sim                           true
% 2.17/0.98  --prep_unflatten                        true
% 2.17/0.98  --prep_res_sim                          true
% 2.17/0.98  --prep_upred                            true
% 2.17/0.98  --prep_sem_filter                       exhaustive
% 2.17/0.98  --prep_sem_filter_out                   false
% 2.17/0.98  --pred_elim                             true
% 2.17/0.98  --res_sim_input                         true
% 2.17/0.98  --eq_ax_congr_red                       true
% 2.17/0.98  --pure_diseq_elim                       true
% 2.17/0.98  --brand_transform                       false
% 2.17/0.98  --non_eq_to_eq                          false
% 2.17/0.98  --prep_def_merge                        true
% 2.17/0.98  --prep_def_merge_prop_impl              false
% 2.17/0.98  --prep_def_merge_mbd                    true
% 2.17/0.98  --prep_def_merge_tr_red                 false
% 2.17/0.98  --prep_def_merge_tr_cl                  false
% 2.17/0.98  --smt_preprocessing                     true
% 2.17/0.98  --smt_ac_axioms                         fast
% 2.17/0.98  --preprocessed_out                      false
% 2.17/0.98  --preprocessed_stats                    false
% 2.17/0.98  
% 2.17/0.98  ------ Abstraction refinement Options
% 2.17/0.98  
% 2.17/0.98  --abstr_ref                             []
% 2.17/0.98  --abstr_ref_prep                        false
% 2.17/0.98  --abstr_ref_until_sat                   false
% 2.17/0.98  --abstr_ref_sig_restrict                funpre
% 2.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.98  --abstr_ref_under                       []
% 2.17/0.98  
% 2.17/0.98  ------ SAT Options
% 2.17/0.98  
% 2.17/0.98  --sat_mode                              false
% 2.17/0.98  --sat_fm_restart_options                ""
% 2.17/0.98  --sat_gr_def                            false
% 2.17/0.98  --sat_epr_types                         true
% 2.17/0.98  --sat_non_cyclic_types                  false
% 2.17/0.98  --sat_finite_models                     false
% 2.17/0.98  --sat_fm_lemmas                         false
% 2.17/0.98  --sat_fm_prep                           false
% 2.17/0.98  --sat_fm_uc_incr                        true
% 2.17/0.98  --sat_out_model                         small
% 2.17/0.98  --sat_out_clauses                       false
% 2.17/0.98  
% 2.17/0.98  ------ QBF Options
% 2.17/0.98  
% 2.17/0.98  --qbf_mode                              false
% 2.17/0.98  --qbf_elim_univ                         false
% 2.17/0.98  --qbf_dom_inst                          none
% 2.17/0.98  --qbf_dom_pre_inst                      false
% 2.17/0.98  --qbf_sk_in                             false
% 2.17/0.98  --qbf_pred_elim                         true
% 2.17/0.98  --qbf_split                             512
% 2.17/0.98  
% 2.17/0.98  ------ BMC1 Options
% 2.17/0.98  
% 2.17/0.98  --bmc1_incremental                      false
% 2.17/0.98  --bmc1_axioms                           reachable_all
% 2.17/0.98  --bmc1_min_bound                        0
% 2.17/0.98  --bmc1_max_bound                        -1
% 2.17/0.98  --bmc1_max_bound_default                -1
% 2.17/0.98  --bmc1_symbol_reachability              true
% 2.17/0.98  --bmc1_property_lemmas                  false
% 2.17/0.98  --bmc1_k_induction                      false
% 2.17/0.98  --bmc1_non_equiv_states                 false
% 2.17/0.98  --bmc1_deadlock                         false
% 2.17/0.98  --bmc1_ucm                              false
% 2.17/0.98  --bmc1_add_unsat_core                   none
% 2.17/0.98  --bmc1_unsat_core_children              false
% 2.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.98  --bmc1_out_stat                         full
% 2.17/0.98  --bmc1_ground_init                      false
% 2.17/0.98  --bmc1_pre_inst_next_state              false
% 2.17/0.98  --bmc1_pre_inst_state                   false
% 2.17/0.98  --bmc1_pre_inst_reach_state             false
% 2.17/0.98  --bmc1_out_unsat_core                   false
% 2.17/0.98  --bmc1_aig_witness_out                  false
% 2.17/0.98  --bmc1_verbose                          false
% 2.17/0.98  --bmc1_dump_clauses_tptp                false
% 2.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.98  --bmc1_dump_file                        -
% 2.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.98  --bmc1_ucm_extend_mode                  1
% 2.17/0.98  --bmc1_ucm_init_mode                    2
% 2.17/0.98  --bmc1_ucm_cone_mode                    none
% 2.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.98  --bmc1_ucm_relax_model                  4
% 2.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.98  --bmc1_ucm_layered_model                none
% 2.17/0.98  --bmc1_ucm_max_lemma_size               10
% 2.17/0.98  
% 2.17/0.98  ------ AIG Options
% 2.17/0.98  
% 2.17/0.98  --aig_mode                              false
% 2.17/0.98  
% 2.17/0.98  ------ Instantiation Options
% 2.17/0.98  
% 2.17/0.98  --instantiation_flag                    true
% 2.17/0.98  --inst_sos_flag                         false
% 2.17/0.98  --inst_sos_phase                        true
% 2.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.98  --inst_lit_sel_side                     none
% 2.17/0.98  --inst_solver_per_active                1400
% 2.17/0.98  --inst_solver_calls_frac                1.
% 2.17/0.98  --inst_passive_queue_type               priority_queues
% 2.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.98  --inst_passive_queues_freq              [25;2]
% 2.17/0.98  --inst_dismatching                      true
% 2.17/0.98  --inst_eager_unprocessed_to_passive     true
% 2.17/0.98  --inst_prop_sim_given                   true
% 2.17/0.98  --inst_prop_sim_new                     false
% 2.17/0.98  --inst_subs_new                         false
% 2.17/0.98  --inst_eq_res_simp                      false
% 2.17/0.98  --inst_subs_given                       false
% 2.17/0.98  --inst_orphan_elimination               true
% 2.17/0.98  --inst_learning_loop_flag               true
% 2.17/0.98  --inst_learning_start                   3000
% 2.17/0.98  --inst_learning_factor                  2
% 2.17/0.98  --inst_start_prop_sim_after_learn       3
% 2.17/0.98  --inst_sel_renew                        solver
% 2.17/0.98  --inst_lit_activity_flag                true
% 2.17/0.98  --inst_restr_to_given                   false
% 2.17/0.98  --inst_activity_threshold               500
% 2.17/0.98  --inst_out_proof                        true
% 2.17/0.98  
% 2.17/0.98  ------ Resolution Options
% 2.17/0.98  
% 2.17/0.98  --resolution_flag                       false
% 2.17/0.98  --res_lit_sel                           adaptive
% 2.17/0.98  --res_lit_sel_side                      none
% 2.17/0.98  --res_ordering                          kbo
% 2.17/0.98  --res_to_prop_solver                    active
% 2.17/0.98  --res_prop_simpl_new                    false
% 2.17/0.98  --res_prop_simpl_given                  true
% 2.17/0.98  --res_passive_queue_type                priority_queues
% 2.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.98  --res_passive_queues_freq               [15;5]
% 2.17/0.98  --res_forward_subs                      full
% 2.17/0.98  --res_backward_subs                     full
% 2.17/0.98  --res_forward_subs_resolution           true
% 2.17/0.98  --res_backward_subs_resolution          true
% 2.17/0.98  --res_orphan_elimination                true
% 2.17/0.98  --res_time_limit                        2.
% 2.17/0.98  --res_out_proof                         true
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Options
% 2.17/0.98  
% 2.17/0.98  --superposition_flag                    true
% 2.17/0.98  --sup_passive_queue_type                priority_queues
% 2.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.98  --demod_completeness_check              fast
% 2.17/0.98  --demod_use_ground                      true
% 2.17/0.98  --sup_to_prop_solver                    passive
% 2.17/0.98  --sup_prop_simpl_new                    true
% 2.17/0.98  --sup_prop_simpl_given                  true
% 2.17/0.98  --sup_fun_splitting                     false
% 2.17/0.98  --sup_smt_interval                      50000
% 2.17/0.98  
% 2.17/0.98  ------ Superposition Simplification Setup
% 2.17/0.98  
% 2.17/0.98  --sup_indices_passive                   []
% 2.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_full_bw                           [BwDemod]
% 2.17/0.98  --sup_immed_triv                        [TrivRules]
% 2.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_immed_bw_main                     []
% 2.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.98  
% 2.17/0.98  ------ Combination Options
% 2.17/0.98  
% 2.17/0.98  --comb_res_mult                         3
% 2.17/0.98  --comb_sup_mult                         2
% 2.17/0.98  --comb_inst_mult                        10
% 2.17/0.98  
% 2.17/0.98  ------ Debug Options
% 2.17/0.98  
% 2.17/0.98  --dbg_backtrace                         false
% 2.17/0.98  --dbg_dump_prop_clauses                 false
% 2.17/0.98  --dbg_dump_prop_clauses_file            -
% 2.17/0.98  --dbg_out_stat                          false
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ Proving...
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  % SZS output start Saturation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  fof(f1,axiom,(
% 2.17/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f15,plain,(
% 2.17/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.98    inference(nnf_transformation,[],[f1])).
% 2.17/0.98  
% 2.17/0.98  fof(f16,plain,(
% 2.17/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.98    inference(flattening,[],[f15])).
% 2.17/0.98  
% 2.17/0.98  fof(f21,plain,(
% 2.17/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.17/0.98    inference(cnf_transformation,[],[f16])).
% 2.17/0.98  
% 2.17/0.98  fof(f44,plain,(
% 2.17/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.17/0.98    inference(equality_resolution,[],[f21])).
% 2.17/0.98  
% 2.17/0.98  fof(f2,axiom,(
% 2.17/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f17,plain,(
% 2.17/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.17/0.98    inference(nnf_transformation,[],[f2])).
% 2.17/0.98  
% 2.17/0.98  fof(f25,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f17])).
% 2.17/0.98  
% 2.17/0.98  fof(f3,axiom,(
% 2.17/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f26,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.17/0.98    inference(cnf_transformation,[],[f3])).
% 2.17/0.98  
% 2.17/0.98  fof(f8,axiom,(
% 2.17/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f31,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.17/0.98    inference(cnf_transformation,[],[f8])).
% 2.17/0.98  
% 2.17/0.98  fof(f39,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.17/0.98    inference(definition_unfolding,[],[f26,f31])).
% 2.17/0.98  
% 2.17/0.98  fof(f40,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X0,X1)) )),
% 2.17/0.98    inference(definition_unfolding,[],[f25,f39])).
% 2.17/0.98  
% 2.17/0.98  fof(f6,axiom,(
% 2.17/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f29,plain,(
% 2.17/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.17/0.98    inference(cnf_transformation,[],[f6])).
% 2.17/0.98  
% 2.17/0.98  fof(f5,axiom,(
% 2.17/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f28,plain,(
% 2.17/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.17/0.98    inference(cnf_transformation,[],[f5])).
% 2.17/0.98  
% 2.17/0.98  fof(f7,axiom,(
% 2.17/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f12,plain,(
% 2.17/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.17/0.98    inference(ennf_transformation,[],[f7])).
% 2.17/0.98  
% 2.17/0.98  fof(f30,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.17/0.98    inference(cnf_transformation,[],[f12])).
% 2.17/0.98  
% 2.17/0.98  fof(f42,plain,(
% 2.17/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.17/0.98    inference(definition_unfolding,[],[f30,f39])).
% 2.17/0.98  
% 2.17/0.98  fof(f10,conjecture,(
% 2.17/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f11,negated_conjecture,(
% 2.17/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.17/0.98    inference(negated_conjecture,[],[f10])).
% 2.17/0.98  
% 2.17/0.98  fof(f14,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 2.17/0.98    inference(ennf_transformation,[],[f11])).
% 2.17/0.98  
% 2.17/0.98  fof(f19,plain,(
% 2.17/0.98    ( ! [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(X0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) & k2_struct_0(X0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f18,plain,(
% 2.17/0.98    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0)) => (? [X1] : (((k2_struct_0(sK0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) & k2_struct_0(sK0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0))),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f20,plain,(
% 2.17/0.98    (((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0)),
% 2.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19,f18])).
% 2.17/0.98  
% 2.17/0.98  fof(f34,plain,(
% 2.17/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.17/0.98    inference(cnf_transformation,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f4,axiom,(
% 2.17/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f27,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f4])).
% 2.17/0.98  
% 2.17/0.98  fof(f24,plain,(
% 2.17/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.17/0.98    inference(cnf_transformation,[],[f17])).
% 2.17/0.98  
% 2.17/0.98  fof(f41,plain,(
% 2.17/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.17/0.98    inference(definition_unfolding,[],[f24,f39])).
% 2.17/0.98  
% 2.17/0.98  fof(f9,axiom,(
% 2.17/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f13,plain,(
% 2.17/0.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 2.17/0.98    inference(ennf_transformation,[],[f9])).
% 2.17/0.98  
% 2.17/0.98  fof(f32,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f13])).
% 2.17/0.98  
% 2.17/0.98  fof(f33,plain,(
% 2.17/0.98    l1_struct_0(sK0)),
% 2.17/0.98    inference(cnf_transformation,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f38,plain,(
% 2.17/0.98    k2_struct_0(sK0) = sK1 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 2.17/0.98    inference(cnf_transformation,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  fof(f23,plain,(
% 2.17/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f16])).
% 2.17/0.98  
% 2.17/0.98  fof(f35,plain,(
% 2.17/0.98    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1),
% 2.17/0.98    inference(cnf_transformation,[],[f20])).
% 2.17/0.98  
% 2.17/0.98  cnf(c_145,plain,
% 2.17/0.98      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | X1 != X0 ),
% 2.17/0.98      theory(equality) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_338,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f44]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_591,plain,
% 2.17/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3,plain,
% 2.17/0.98      ( ~ r1_tarski(X0,X1)
% 2.17/0.98      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 2.17/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_590,plain,
% 2.17/0.98      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0
% 2.17/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_7,plain,
% 2.17/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_588,plain,
% 2.17/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_6,plain,
% 2.17/0.98      ( k2_subset_1(X0) = X0 ),
% 2.17/0.98      inference(cnf_transformation,[],[f28]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_599,plain,
% 2.17/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.17/0.98      inference(light_normalisation,[status(thm)],[c_588,c_6]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_8,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.98      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.17/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_587,plain,
% 2.17/0.98      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1010,plain,
% 2.17/0.98      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_599,c_587]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1395,plain,
% 2.17/0.98      ( k7_subset_1(X0,X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_590,c_1010]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1401,plain,
% 2.17/0.98      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_591,c_1395]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_14,negated_conjecture,
% 2.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.17/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_586,plain,
% 2.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_835,plain,
% 2.17/0.98      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_586,c_587]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1216,plain,
% 2.17/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_1010,c_835]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_5,plain,
% 2.17/0.98      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1061,plain,
% 2.17/0.98      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_5,c_835]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1242,plain,
% 2.17/0.98      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(sK1,sK1,X0) ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_1216,c_1061]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4,plain,
% 2.17/0.98      ( r1_tarski(X0,X1)
% 2.17/0.98      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != k1_xboole_0 ),
% 2.17/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_589,plain,
% 2.17/0.98      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != k1_xboole_0
% 2.17/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1063,plain,
% 2.17/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) != k1_xboole_0
% 2.17/0.98      | r1_tarski(sK1,X0) = iProver_top ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_835,c_589]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1241,plain,
% 2.17/0.98      ( k7_subset_1(sK1,sK1,X0) != k1_xboole_0
% 2.17/0.98      | r1_tarski(sK1,X0) = iProver_top ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_1216,c_1063]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1233,plain,
% 2.17/0.98      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_5,c_1010]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1215,plain,
% 2.17/0.98      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_1010,c_587]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1214,plain,
% 2.17/0.98      ( k7_subset_1(X0,X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 2.17/0.98      inference(demodulation,[status(thm)],[c_1010,c_589]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_9,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.98      | ~ l1_struct_0(X1)
% 2.17/0.98      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 2.17/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_15,negated_conjecture,
% 2.17/0.98      ( l1_struct_0(sK0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_155,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.17/0.98      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
% 2.17/0.98      | sK0 != X1 ),
% 2.17/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_156,plain,
% 2.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.17/0.98      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
% 2.17/0.98      inference(unflattening,[status(thm)],[c_155]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_585,plain,
% 2.17/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 2.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.17/0.98      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1011,plain,
% 2.17/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 2.17/0.98      inference(superposition,[status(thm)],[c_599,c_585]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_10,negated_conjecture,
% 2.17/0.99      ( k2_struct_0(sK0) = sK1
% 2.17/0.99      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_687,plain,
% 2.17/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_586,c_585]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_778,plain,
% 2.17/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
% 2.17/0.99      | k2_struct_0(sK0) = sK1 ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_10,c_687]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_0,plain,
% 2.17/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.17/0.99      inference(cnf_transformation,[],[f23]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_592,plain,
% 2.17/0.99      ( X0 = X1
% 2.17/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.17/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_13,negated_conjecture,
% 2.17/0.99      ( k2_struct_0(sK0) != sK1
% 2.17/0.99      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  % SZS output end Saturation for theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  ------                               Statistics
% 2.17/0.99  
% 2.17/0.99  ------ General
% 2.17/0.99  
% 2.17/0.99  abstr_ref_over_cycles:                  0
% 2.17/0.99  abstr_ref_under_cycles:                 0
% 2.17/0.99  gc_basic_clause_elim:                   0
% 2.17/0.99  forced_gc_time:                         0
% 2.17/0.99  parsing_time:                           0.009
% 2.17/0.99  unif_index_cands_time:                  0.
% 2.17/0.99  unif_index_add_time:                    0.
% 2.17/0.99  orderings_time:                         0.
% 2.17/0.99  out_proof_time:                         0.
% 2.17/0.99  total_time:                             0.086
% 2.17/0.99  num_of_symbols:                         45
% 2.17/0.99  num_of_terms:                           1468
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing
% 2.17/0.99  
% 2.17/0.99  num_of_splits:                          0
% 2.17/0.99  num_of_split_atoms:                     0
% 2.17/0.99  num_of_reused_defs:                     0
% 2.17/0.99  num_eq_ax_congr_red:                    18
% 2.17/0.99  num_of_sem_filtered_clauses:            1
% 2.17/0.99  num_of_subtypes:                        0
% 2.17/0.99  monotx_restored_types:                  0
% 2.17/0.99  sat_num_of_epr_types:                   0
% 2.17/0.99  sat_num_of_non_cyclic_types:            0
% 2.17/0.99  sat_guarded_non_collapsed_types:        0
% 2.17/0.99  num_pure_diseq_elim:                    0
% 2.17/0.99  simp_replaced_by:                       0
% 2.17/0.99  res_preprocessed:                       68
% 2.17/0.99  prep_upred:                             0
% 2.17/0.99  prep_unflattend:                        9
% 2.17/0.99  smt_new_axioms:                         0
% 2.17/0.99  pred_elim_cands:                        2
% 2.17/0.99  pred_elim:                              1
% 2.17/0.99  pred_elim_cl:                           1
% 2.17/0.99  pred_elim_cycles:                       3
% 2.17/0.99  merged_defs:                            16
% 2.17/0.99  merged_defs_ncl:                        0
% 2.17/0.99  bin_hyper_res:                          16
% 2.17/0.99  prep_cycles:                            4
% 2.17/0.99  pred_elim_time:                         0.001
% 2.17/0.99  splitting_time:                         0.
% 2.17/0.99  sem_filter_time:                        0.
% 2.17/0.99  monotx_time:                            0.
% 2.17/0.99  subtype_inf_time:                       0.
% 2.17/0.99  
% 2.17/0.99  ------ Problem properties
% 2.17/0.99  
% 2.17/0.99  clauses:                                12
% 2.17/0.99  conjectures:                            3
% 2.17/0.99  epr:                                    2
% 2.17/0.99  horn:                                   11
% 2.17/0.99  ground:                                 3
% 2.17/0.99  unary:                                  5
% 2.17/0.99  binary:                                 6
% 2.17/0.99  lits:                                   20
% 2.17/0.99  lits_eq:                                11
% 2.17/0.99  fd_pure:                                0
% 2.17/0.99  fd_pseudo:                              0
% 2.17/0.99  fd_cond:                                0
% 2.17/0.99  fd_pseudo_cond:                         1
% 2.17/0.99  ac_symbols:                             0
% 2.17/0.99  
% 2.17/0.99  ------ Propositional Solver
% 2.17/0.99  
% 2.17/0.99  prop_solver_calls:                      27
% 2.17/0.99  prop_fast_solver_calls:                 315
% 2.17/0.99  smt_solver_calls:                       0
% 2.17/0.99  smt_fast_solver_calls:                  0
% 2.17/0.99  prop_num_of_clauses:                    514
% 2.17/0.99  prop_preprocess_simplified:             2138
% 2.17/0.99  prop_fo_subsumed:                       0
% 2.17/0.99  prop_solver_time:                       0.
% 2.17/0.99  smt_solver_time:                        0.
% 2.17/0.99  smt_fast_solver_time:                   0.
% 2.17/0.99  prop_fast_solver_time:                  0.
% 2.17/0.99  prop_unsat_core_time:                   0.
% 2.17/0.99  
% 2.17/0.99  ------ QBF
% 2.17/0.99  
% 2.17/0.99  qbf_q_res:                              0
% 2.17/0.99  qbf_num_tautologies:                    0
% 2.17/0.99  qbf_prep_cycles:                        0
% 2.17/0.99  
% 2.17/0.99  ------ BMC1
% 2.17/0.99  
% 2.17/0.99  bmc1_current_bound:                     -1
% 2.17/0.99  bmc1_last_solved_bound:                 -1
% 2.17/0.99  bmc1_unsat_core_size:                   -1
% 2.17/0.99  bmc1_unsat_core_parents_size:           -1
% 2.17/0.99  bmc1_merge_next_fun:                    0
% 2.17/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.99  
% 2.17/0.99  ------ Instantiation
% 2.17/0.99  
% 2.17/0.99  inst_num_of_clauses:                    189
% 2.17/0.99  inst_num_in_passive:                    26
% 2.17/0.99  inst_num_in_active:                     135
% 2.17/0.99  inst_num_in_unprocessed:                28
% 2.17/0.99  inst_num_of_loops:                      140
% 2.17/0.99  inst_num_of_learning_restarts:          0
% 2.17/0.99  inst_num_moves_active_passive:          2
% 2.17/0.99  inst_lit_activity:                      0
% 2.17/0.99  inst_lit_activity_moves:                0
% 2.17/0.99  inst_num_tautologies:                   0
% 2.17/0.99  inst_num_prop_implied:                  0
% 2.17/0.99  inst_num_existing_simplified:           0
% 2.17/0.99  inst_num_eq_res_simplified:             0
% 2.17/0.99  inst_num_child_elim:                    0
% 2.17/0.99  inst_num_of_dismatching_blockings:      113
% 2.17/0.99  inst_num_of_non_proper_insts:           240
% 2.17/0.99  inst_num_of_duplicates:                 0
% 2.17/0.99  inst_inst_num_from_inst_to_res:         0
% 2.17/0.99  inst_dismatching_checking_time:         0.
% 2.17/0.99  
% 2.17/0.99  ------ Resolution
% 2.17/0.99  
% 2.17/0.99  res_num_of_clauses:                     0
% 2.17/0.99  res_num_in_passive:                     0
% 2.17/0.99  res_num_in_active:                      0
% 2.17/0.99  res_num_of_loops:                       72
% 2.17/0.99  res_forward_subset_subsumed:            28
% 2.17/0.99  res_backward_subset_subsumed:           0
% 2.17/0.99  res_forward_subsumed:                   0
% 2.17/0.99  res_backward_subsumed:                  0
% 2.17/0.99  res_forward_subsumption_resolution:     0
% 2.17/0.99  res_backward_subsumption_resolution:    0
% 2.17/0.99  res_clause_to_clause_subsumption:       68
% 2.17/0.99  res_orphan_elimination:                 0
% 2.17/0.99  res_tautology_del:                      50
% 2.17/0.99  res_num_eq_res_simplified:              0
% 2.17/0.99  res_num_sel_changes:                    0
% 2.17/0.99  res_moves_from_active_to_pass:          0
% 2.17/0.99  
% 2.17/0.99  ------ Superposition
% 2.17/0.99  
% 2.17/0.99  sup_time_total:                         0.
% 2.17/0.99  sup_time_generating:                    0.
% 2.17/0.99  sup_time_sim_full:                      0.
% 2.17/0.99  sup_time_sim_immed:                     0.
% 2.17/0.99  
% 2.17/0.99  sup_num_of_clauses:                     25
% 2.17/0.99  sup_num_in_active:                      21
% 2.17/0.99  sup_num_in_passive:                     4
% 2.17/0.99  sup_num_of_loops:                       26
% 2.17/0.99  sup_fw_superposition:                   22
% 2.17/0.99  sup_bw_superposition:                   6
% 2.17/0.99  sup_immediate_simplified:               3
% 2.17/0.99  sup_given_eliminated:                   0
% 2.17/0.99  comparisons_done:                       0
% 2.17/0.99  comparisons_avoided:                    0
% 2.17/0.99  
% 2.17/0.99  ------ Simplifications
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  sim_fw_subset_subsumed:                 0
% 2.17/0.99  sim_bw_subset_subsumed:                 0
% 2.17/0.99  sim_fw_subsumed:                        4
% 2.17/0.99  sim_bw_subsumed:                        0
% 2.17/0.99  sim_fw_subsumption_res:                 0
% 2.17/0.99  sim_bw_subsumption_res:                 0
% 2.17/0.99  sim_tautology_del:                      1
% 2.17/0.99  sim_eq_tautology_del:                   2
% 2.17/0.99  sim_eq_res_simp:                        0
% 2.17/0.99  sim_fw_demodulated:                     1
% 2.17/0.99  sim_bw_demodulated:                     5
% 2.17/0.99  sim_light_normalised:                   2
% 2.17/0.99  sim_joinable_taut:                      0
% 2.17/0.99  sim_joinable_simp:                      0
% 2.17/0.99  sim_ac_normalised:                      0
% 2.17/0.99  sim_smt_subsumption:                    0
% 2.17/0.99  
%------------------------------------------------------------------------------
