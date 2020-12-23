%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:25 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 144 expanded)
%              Number of clauses        :   55 (  64 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  236 ( 323 expanded)
%              Number of equality atoms :   64 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,
    ( ? [X0] :
        ( k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0)
        & l1_pre_topc(X0) )
   => ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f34])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2038,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),X0)
    | X0 = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4491,plain,
    ( ~ r1_tarski(k2_pre_topc(X0,u1_struct_0(X0)),u1_struct_0(X0))
    | ~ r1_tarski(u1_struct_0(X0),k2_pre_topc(X0,u1_struct_0(X0)))
    | k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2038])).

cnf(c_4493,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_pre_topc(sK1,u1_struct_0(sK1)))
    | k2_pre_topc(sK1,u1_struct_0(sK1)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4491])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_861,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_857,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_852,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1471,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_852])).

cnf(c_2232,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_1471])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_855,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2791,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_2232,c_855])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_152,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_187,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_153])).

cnf(c_844,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_1814,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_857,c_844])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_845,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_848,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1065,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_845,c_848])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_847,plain,
    ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1933,plain,
    ( k3_subset_1(u1_struct_0(sK1),k1_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1065,c_847])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_851,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1233,plain,
    ( k1_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1065,c_851])).

cnf(c_1934,plain,
    ( k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1933,c_1233])).

cnf(c_2089,plain,
    ( k4_xboole_0(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1814,c_1934])).

cnf(c_2942,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2791,c_2089])).

cnf(c_19,negated_conjecture,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2952,plain,
    ( k2_pre_topc(sK1,u1_struct_0(sK1)) != u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2942,c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2277,plain,
    ( ~ m1_subset_1(k2_pre_topc(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(k2_pre_topc(X0,u1_struct_0(X0)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_2289,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k2_pre_topc(sK1,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2277])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1546,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(u1_struct_0(X0),k2_pre_topc(X0,u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1553,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(u1_struct_0(sK1),k2_pre_topc(sK1,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1547,plain,
    ( m1_subset_1(k2_pre_topc(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1549,plain,
    ( m1_subset_1(k2_pre_topc(sK1,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1179,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1185,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_1052,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1178,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_1181,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4493,c_2952,c_2289,c_1553,c_1549,c_1185,c_1181,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.09/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/0.98  
% 3.09/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/0.98  
% 3.09/0.98  ------  iProver source info
% 3.09/0.98  
% 3.09/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.09/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/0.98  git: non_committed_changes: false
% 3.09/0.98  git: last_make_outside_of_git: false
% 3.09/0.98  
% 3.09/0.98  ------ 
% 3.09/0.98  ------ Parsing...
% 3.09/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/0.98  
% 3.09/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.09/0.98  
% 3.09/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/0.98  
% 3.09/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/0.98  ------ Proving...
% 3.09/0.98  ------ Problem Properties 
% 3.09/0.98  
% 3.09/0.98  
% 3.09/0.98  clauses                                 20
% 3.09/0.98  conjectures                             2
% 3.09/0.98  EPR                                     7
% 3.09/0.98  Horn                                    18
% 3.09/0.98  unary                                   4
% 3.09/0.98  binary                                  12
% 3.09/0.98  lits                                    40
% 3.09/0.98  lits eq                                 7
% 3.09/0.98  fd_pure                                 0
% 3.09/0.98  fd_pseudo                               0
% 3.09/0.98  fd_cond                                 0
% 3.09/0.98  fd_pseudo_cond                          1
% 3.09/0.98  AC symbols                              0
% 3.09/0.98  
% 3.09/0.98  ------ Input Options Time Limit: Unbounded
% 3.09/0.98  
% 3.09/0.98  
% 3.09/0.98  ------ 
% 3.09/0.98  Current options:
% 3.09/0.98  ------ 
% 3.09/0.98  
% 3.09/0.98  
% 3.09/0.98  
% 3.09/0.98  
% 3.09/0.98  ------ Proving...
% 3.09/0.98  
% 3.09/0.98  
% 3.09/0.98  % SZS status Theorem for theBenchmark.p
% 3.09/0.98  
% 3.09/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/0.98  
% 3.09/0.98  fof(f2,axiom,(
% 3.09/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f30,plain,(
% 3.09/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/0.98    inference(nnf_transformation,[],[f2])).
% 3.09/0.98  
% 3.09/0.98  fof(f31,plain,(
% 3.09/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/0.98    inference(flattening,[],[f30])).
% 3.09/0.98  
% 3.09/0.98  fof(f41,plain,(
% 3.09/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f31])).
% 3.09/0.98  
% 3.09/0.98  fof(f1,axiom,(
% 3.09/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f16,plain,(
% 3.09/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.09/0.98    inference(rectify,[],[f1])).
% 3.09/0.98  
% 3.09/0.98  fof(f17,plain,(
% 3.09/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.09/0.98    inference(ennf_transformation,[],[f16])).
% 3.09/0.98  
% 3.09/0.98  fof(f28,plain,(
% 3.09/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.09/0.98    introduced(choice_axiom,[])).
% 3.09/0.98  
% 3.09/0.98  fof(f29,plain,(
% 3.09/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.09/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f28])).
% 3.09/0.98  
% 3.09/0.98  fof(f37,plain,(
% 3.09/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f29])).
% 3.09/0.98  
% 3.09/0.98  fof(f3,axiom,(
% 3.09/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f42,plain,(
% 3.09/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f3])).
% 3.09/0.98  
% 3.09/0.98  fof(f7,axiom,(
% 3.09/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f19,plain,(
% 3.09/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.09/0.98    inference(ennf_transformation,[],[f7])).
% 3.09/0.98  
% 3.09/0.98  fof(f48,plain,(
% 3.09/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f19])).
% 3.09/0.98  
% 3.09/0.98  fof(f4,axiom,(
% 3.09/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f32,plain,(
% 3.09/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.09/0.98    inference(nnf_transformation,[],[f4])).
% 3.09/0.98  
% 3.09/0.98  fof(f43,plain,(
% 3.09/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f32])).
% 3.09/0.98  
% 3.09/0.98  fof(f5,axiom,(
% 3.09/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f18,plain,(
% 3.09/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.09/0.98    inference(ennf_transformation,[],[f5])).
% 3.09/0.98  
% 3.09/0.98  fof(f45,plain,(
% 3.09/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.09/0.98    inference(cnf_transformation,[],[f18])).
% 3.09/0.98  
% 3.09/0.98  fof(f6,axiom,(
% 3.09/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f33,plain,(
% 3.09/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.09/0.98    inference(nnf_transformation,[],[f6])).
% 3.09/0.98  
% 3.09/0.98  fof(f47,plain,(
% 3.09/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f33])).
% 3.09/0.98  
% 3.09/0.98  fof(f14,conjecture,(
% 3.09/0.98    ! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f15,negated_conjecture,(
% 3.09/0.98    ~! [X0] : (l1_pre_topc(X0) => k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0))),
% 3.09/0.98    inference(negated_conjecture,[],[f14])).
% 3.09/0.98  
% 3.09/0.98  fof(f27,plain,(
% 3.09/0.98    ? [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0) & l1_pre_topc(X0))),
% 3.09/0.98    inference(ennf_transformation,[],[f15])).
% 3.09/0.98  
% 3.09/0.98  fof(f34,plain,(
% 3.09/0.98    ? [X0] : (k2_pre_topc(X0,k2_struct_0(X0)) != k2_struct_0(X0) & l1_pre_topc(X0)) => (k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) & l1_pre_topc(sK1))),
% 3.09/0.98    introduced(choice_axiom,[])).
% 3.09/0.98  
% 3.09/0.98  fof(f35,plain,(
% 3.09/0.98    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) & l1_pre_topc(sK1)),
% 3.09/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f34])).
% 3.09/0.98  
% 3.09/0.98  fof(f55,plain,(
% 3.09/0.98    l1_pre_topc(sK1)),
% 3.09/0.98    inference(cnf_transformation,[],[f35])).
% 3.09/0.98  
% 3.09/0.98  fof(f11,axiom,(
% 3.09/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f24,plain,(
% 3.09/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.09/0.98    inference(ennf_transformation,[],[f11])).
% 3.09/0.98  
% 3.09/0.98  fof(f52,plain,(
% 3.09/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f24])).
% 3.09/0.98  
% 3.09/0.98  fof(f12,axiom,(
% 3.09/0.98    ! [X0] : (l1_struct_0(X0) => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f25,plain,(
% 3.09/0.98    ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.09/0.98    inference(ennf_transformation,[],[f12])).
% 3.09/0.98  
% 3.09/0.98  fof(f53,plain,(
% 3.09/0.98    ( ! [X0] : (k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f25])).
% 3.09/0.98  
% 3.09/0.98  fof(f8,axiom,(
% 3.09/0.98    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f20,plain,(
% 3.09/0.98    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.09/0.98    inference(ennf_transformation,[],[f8])).
% 3.09/0.98  
% 3.09/0.98  fof(f49,plain,(
% 3.09/0.98    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f20])).
% 3.09/0.98  
% 3.09/0.98  fof(f56,plain,(
% 3.09/0.98    k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1)),
% 3.09/0.98    inference(cnf_transformation,[],[f35])).
% 3.09/0.98  
% 3.09/0.98  fof(f46,plain,(
% 3.09/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.09/0.98    inference(cnf_transformation,[],[f33])).
% 3.09/0.98  
% 3.09/0.98  fof(f13,axiom,(
% 3.09/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f26,plain,(
% 3.09/0.98    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.09/0.98    inference(ennf_transformation,[],[f13])).
% 3.09/0.98  
% 3.09/0.98  fof(f54,plain,(
% 3.09/0.98    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f26])).
% 3.09/0.98  
% 3.09/0.98  fof(f10,axiom,(
% 3.09/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.09/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/0.98  
% 3.09/0.98  fof(f22,plain,(
% 3.09/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.09/0.98    inference(ennf_transformation,[],[f10])).
% 3.09/0.98  
% 3.09/0.98  fof(f23,plain,(
% 3.09/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.09/0.98    inference(flattening,[],[f22])).
% 3.09/0.98  
% 3.09/0.98  fof(f51,plain,(
% 3.09/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.09/0.98    inference(cnf_transformation,[],[f23])).
% 3.09/0.98  
% 3.09/0.98  fof(f40,plain,(
% 3.09/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.09/0.98    inference(cnf_transformation,[],[f31])).
% 3.09/0.98  
% 3.09/0.98  fof(f57,plain,(
% 3.09/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.09/0.98    inference(equality_resolution,[],[f40])).
% 3.09/0.98  
% 3.09/0.98  cnf(c_3,plain,
% 3.09/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.09/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_2038,plain,
% 3.09/0.98      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 3.09/0.98      | ~ r1_tarski(u1_struct_0(X1),X0)
% 3.09/0.98      | X0 = u1_struct_0(X1) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_4491,plain,
% 3.09/0.98      ( ~ r1_tarski(k2_pre_topc(X0,u1_struct_0(X0)),u1_struct_0(X0))
% 3.09/0.98      | ~ r1_tarski(u1_struct_0(X0),k2_pre_topc(X0,u1_struct_0(X0)))
% 3.09/0.98      | k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_2038]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_4493,plain,
% 3.09/0.98      ( ~ r1_tarski(k2_pre_topc(sK1,u1_struct_0(sK1)),u1_struct_0(sK1))
% 3.09/0.98      | ~ r1_tarski(u1_struct_0(sK1),k2_pre_topc(sK1,u1_struct_0(sK1)))
% 3.09/0.98      | k2_pre_topc(sK1,u1_struct_0(sK1)) = u1_struct_0(sK1) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_4491]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1,plain,
% 3.09/0.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.09/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_861,plain,
% 3.09/0.98      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.09/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_6,plain,
% 3.09/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.09/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_857,plain,
% 3.09/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_12,plain,
% 3.09/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.09/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_852,plain,
% 3.09/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.09/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1471,plain,
% 3.09/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.09/0.98      inference(superposition,[status(thm)],[c_857,c_852]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_2232,plain,
% 3.09/0.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.09/0.98      inference(superposition,[status(thm)],[c_861,c_1471]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_8,plain,
% 3.09/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.09/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_855,plain,
% 3.09/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_2791,plain,
% 3.09/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.09/0.98      inference(superposition,[status(thm)],[c_2232,c_855]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_9,plain,
% 3.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.09/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.09/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_10,plain,
% 3.09/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.09/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_152,plain,
% 3.09/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.09/0.98      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_153,plain,
% 3.09/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.09/0.98      inference(renaming,[status(thm)],[c_152]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_187,plain,
% 3.09/0.98      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.09/0.98      inference(bin_hyper_res,[status(thm)],[c_9,c_153]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_844,plain,
% 3.09/0.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.09/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1814,plain,
% 3.09/0.98      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.09/0.98      inference(superposition,[status(thm)],[c_857,c_844]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_20,negated_conjecture,
% 3.09/0.98      ( l1_pre_topc(sK1) ),
% 3.09/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_845,plain,
% 3.09/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_16,plain,
% 3.09/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.09/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_848,plain,
% 3.09/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1065,plain,
% 3.09/0.98      ( l1_struct_0(sK1) = iProver_top ),
% 3.09/0.98      inference(superposition,[status(thm)],[c_845,c_848]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_17,plain,
% 3.09/0.98      ( ~ l1_struct_0(X0)
% 3.09/0.98      | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
% 3.09/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_847,plain,
% 3.09/0.98      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
% 3.09/0.98      | l1_struct_0(X0) != iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1933,plain,
% 3.09/0.98      ( k3_subset_1(u1_struct_0(sK1),k1_struct_0(sK1)) = k2_struct_0(sK1) ),
% 3.09/0.98      inference(superposition,[status(thm)],[c_1065,c_847]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_13,plain,
% 3.09/0.98      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 3.09/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_851,plain,
% 3.09/0.98      ( k1_struct_0(X0) = k1_xboole_0 | l1_struct_0(X0) != iProver_top ),
% 3.09/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1233,plain,
% 3.09/0.98      ( k1_struct_0(sK1) = k1_xboole_0 ),
% 3.09/0.98      inference(superposition,[status(thm)],[c_1065,c_851]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1934,plain,
% 3.09/0.98      ( k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1) ),
% 3.09/0.98      inference(light_normalisation,[status(thm)],[c_1933,c_1233]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_2089,plain,
% 3.09/0.98      ( k4_xboole_0(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1) ),
% 3.09/0.98      inference(superposition,[status(thm)],[c_1814,c_1934]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_2942,plain,
% 3.09/0.98      ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
% 3.09/0.98      inference(demodulation,[status(thm)],[c_2791,c_2089]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_19,negated_conjecture,
% 3.09/0.98      ( k2_pre_topc(sK1,k2_struct_0(sK1)) != k2_struct_0(sK1) ),
% 3.09/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_2952,plain,
% 3.09/0.98      ( k2_pre_topc(sK1,u1_struct_0(sK1)) != u1_struct_0(sK1) ),
% 3.09/0.98      inference(demodulation,[status(thm)],[c_2942,c_19]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_11,plain,
% 3.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.09/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1173,plain,
% 3.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/0.98      | r1_tarski(X0,u1_struct_0(X1)) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_2277,plain,
% 3.09/0.98      ( ~ m1_subset_1(k2_pre_topc(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/0.98      | r1_tarski(k2_pre_topc(X0,u1_struct_0(X0)),u1_struct_0(X0)) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_1173]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_2289,plain,
% 3.09/0.98      ( ~ m1_subset_1(k2_pre_topc(sK1,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.09/0.98      | r1_tarski(k2_pre_topc(sK1,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_2277]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_18,plain,
% 3.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/0.98      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.09/0.98      | ~ l1_pre_topc(X1) ),
% 3.09/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1546,plain,
% 3.09/0.98      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/0.98      | r1_tarski(u1_struct_0(X0),k2_pre_topc(X0,u1_struct_0(X0)))
% 3.09/0.98      | ~ l1_pre_topc(X0) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1553,plain,
% 3.09/0.98      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.09/0.98      | r1_tarski(u1_struct_0(sK1),k2_pre_topc(sK1,u1_struct_0(sK1)))
% 3.09/0.98      | ~ l1_pre_topc(sK1) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_1546]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_15,plain,
% 3.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/0.98      | ~ l1_pre_topc(X1) ),
% 3.09/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1547,plain,
% 3.09/0.98      ( m1_subset_1(k2_pre_topc(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/0.98      | ~ l1_pre_topc(X0) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1549,plain,
% 3.09/0.98      ( m1_subset_1(k2_pre_topc(sK1,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.09/0.98      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.09/0.98      | ~ l1_pre_topc(sK1) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_1547]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_4,plain,
% 3.09/0.98      ( r1_tarski(X0,X0) ),
% 3.09/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1179,plain,
% 3.09/0.98      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1185,plain,
% 3.09/0.98      ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_1179]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1052,plain,
% 3.09/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.09/0.98      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1178,plain,
% 3.09/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.09/0.98      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_1052]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(c_1181,plain,
% 3.09/0.98      ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.09/0.98      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) ),
% 3.09/0.98      inference(instantiation,[status(thm)],[c_1178]) ).
% 3.09/0.98  
% 3.09/0.98  cnf(contradiction,plain,
% 3.09/0.98      ( $false ),
% 3.09/0.98      inference(minisat,
% 3.09/0.98                [status(thm)],
% 3.09/0.98                [c_4493,c_2952,c_2289,c_1553,c_1549,c_1185,c_1181,c_20]) ).
% 3.09/0.98  
% 3.09/0.98  
% 3.09/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/0.98  
% 3.09/0.98  ------                               Statistics
% 3.09/0.98  
% 3.09/0.98  ------ Selected
% 3.09/0.98  
% 3.09/0.98  total_time:                             0.166
% 3.09/0.98  
%------------------------------------------------------------------------------
