%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:29 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 287 expanded)
%              Number of clauses        :   57 ( 107 expanded)
%              Number of leaves         :   10 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  254 (1037 expanded)
%              Number of equality atoms :   59 ( 114 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | ~ v4_pre_topc(sK1,X0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_117,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_118,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_117])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_307,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_118,c_13])).

cnf(c_308,plain,
    ( r1_tarski(sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_622,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_212,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_7])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_226,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_14])).

cnf(c_227,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_633,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0)
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_622,c_227])).

cnf(c_695,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_633])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_120,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_119])).

cnf(c_149,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_120])).

cnf(c_626,plain,
    ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_863,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_695,c_626])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_627,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_120])).

cnf(c_625,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_995,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_627,c_625])).

cnf(c_12,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_123,plain,
    ( v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_124,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(renaming,[status(thm)],[c_123])).

cnf(c_9,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_231,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_232,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_272,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_124,c_232])).

cnf(c_273,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_350,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(prop_impl,[status(thm)],[c_13,c_273])).

cnf(c_351,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_624,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_652,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_624,c_227])).

cnf(c_1004,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_995,c_652])).

cnf(c_1151,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_863,c_1004])).

cnf(c_11,negated_conjecture,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_121,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_122,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(renaming,[status(thm)],[c_121])).

cnf(c_8,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_246,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_247,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_286,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_122,c_247])).

cnf(c_287,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_348,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(prop_impl,[status(thm)],[c_13,c_287])).

cnf(c_349,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(renaming,[status(thm)],[c_348])).

cnf(c_623,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_657,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_623,c_227])).

cnf(c_1005,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_995,c_657])).

cnf(c_1152,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_863,c_1005])).

cnf(c_1156,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1151,c_1152])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:01:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.16/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.16/0.98  
% 1.16/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.16/0.98  
% 1.16/0.98  ------  iProver source info
% 1.16/0.98  
% 1.16/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.16/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.16/0.98  git: non_committed_changes: false
% 1.16/0.98  git: last_make_outside_of_git: false
% 1.16/0.98  
% 1.16/0.98  ------ 
% 1.16/0.98  
% 1.16/0.98  ------ Input Options
% 1.16/0.98  
% 1.16/0.98  --out_options                           all
% 1.16/0.98  --tptp_safe_out                         true
% 1.16/0.98  --problem_path                          ""
% 1.16/0.98  --include_path                          ""
% 1.16/0.98  --clausifier                            res/vclausify_rel
% 1.16/0.98  --clausifier_options                    --mode clausify
% 1.16/0.98  --stdin                                 false
% 1.16/0.98  --stats_out                             all
% 1.16/0.98  
% 1.16/0.98  ------ General Options
% 1.16/0.98  
% 1.16/0.98  --fof                                   false
% 1.16/0.98  --time_out_real                         305.
% 1.16/0.98  --time_out_virtual                      -1.
% 1.16/0.98  --symbol_type_check                     false
% 1.16/0.98  --clausify_out                          false
% 1.16/0.98  --sig_cnt_out                           false
% 1.16/0.98  --trig_cnt_out                          false
% 1.16/0.98  --trig_cnt_out_tolerance                1.
% 1.16/0.98  --trig_cnt_out_sk_spl                   false
% 1.16/0.98  --abstr_cl_out                          false
% 1.16/0.98  
% 1.16/0.98  ------ Global Options
% 1.16/0.98  
% 1.16/0.98  --schedule                              default
% 1.16/0.98  --add_important_lit                     false
% 1.16/0.98  --prop_solver_per_cl                    1000
% 1.16/0.98  --min_unsat_core                        false
% 1.16/0.98  --soft_assumptions                      false
% 1.16/0.98  --soft_lemma_size                       3
% 1.16/0.98  --prop_impl_unit_size                   0
% 1.16/0.98  --prop_impl_unit                        []
% 1.16/0.98  --share_sel_clauses                     true
% 1.16/0.98  --reset_solvers                         false
% 1.16/0.98  --bc_imp_inh                            [conj_cone]
% 1.16/0.98  --conj_cone_tolerance                   3.
% 1.16/0.98  --extra_neg_conj                        none
% 1.16/0.98  --large_theory_mode                     true
% 1.16/0.98  --prolific_symb_bound                   200
% 1.16/0.98  --lt_threshold                          2000
% 1.16/0.98  --clause_weak_htbl                      true
% 1.16/0.98  --gc_record_bc_elim                     false
% 1.16/0.98  
% 1.16/0.98  ------ Preprocessing Options
% 1.16/0.98  
% 1.16/0.98  --preprocessing_flag                    true
% 1.16/0.98  --time_out_prep_mult                    0.1
% 1.16/0.98  --splitting_mode                        input
% 1.16/0.98  --splitting_grd                         true
% 1.16/0.98  --splitting_cvd                         false
% 1.16/0.98  --splitting_cvd_svl                     false
% 1.16/0.98  --splitting_nvd                         32
% 1.16/0.98  --sub_typing                            true
% 1.16/0.98  --prep_gs_sim                           true
% 1.16/0.98  --prep_unflatten                        true
% 1.16/0.98  --prep_res_sim                          true
% 1.16/0.98  --prep_upred                            true
% 1.16/0.98  --prep_sem_filter                       exhaustive
% 1.16/0.98  --prep_sem_filter_out                   false
% 1.16/0.98  --pred_elim                             true
% 1.16/0.98  --res_sim_input                         true
% 1.16/0.98  --eq_ax_congr_red                       true
% 1.16/0.98  --pure_diseq_elim                       true
% 1.16/0.98  --brand_transform                       false
% 1.16/0.98  --non_eq_to_eq                          false
% 1.16/0.98  --prep_def_merge                        true
% 1.16/0.98  --prep_def_merge_prop_impl              false
% 1.16/0.98  --prep_def_merge_mbd                    true
% 1.16/0.98  --prep_def_merge_tr_red                 false
% 1.16/0.98  --prep_def_merge_tr_cl                  false
% 1.16/0.98  --smt_preprocessing                     true
% 1.16/0.98  --smt_ac_axioms                         fast
% 1.16/0.98  --preprocessed_out                      false
% 1.16/0.98  --preprocessed_stats                    false
% 1.16/0.98  
% 1.16/0.98  ------ Abstraction refinement Options
% 1.16/0.98  
% 1.16/0.98  --abstr_ref                             []
% 1.16/0.98  --abstr_ref_prep                        false
% 1.16/0.98  --abstr_ref_until_sat                   false
% 1.16/0.98  --abstr_ref_sig_restrict                funpre
% 1.16/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.16/0.98  --abstr_ref_under                       []
% 1.16/0.98  
% 1.16/0.98  ------ SAT Options
% 1.16/0.98  
% 1.16/0.98  --sat_mode                              false
% 1.16/0.98  --sat_fm_restart_options                ""
% 1.16/0.98  --sat_gr_def                            false
% 1.16/0.98  --sat_epr_types                         true
% 1.16/0.98  --sat_non_cyclic_types                  false
% 1.16/0.98  --sat_finite_models                     false
% 1.16/0.98  --sat_fm_lemmas                         false
% 1.16/0.98  --sat_fm_prep                           false
% 1.16/0.98  --sat_fm_uc_incr                        true
% 1.16/0.98  --sat_out_model                         small
% 1.16/0.98  --sat_out_clauses                       false
% 1.16/0.98  
% 1.16/0.98  ------ QBF Options
% 1.16/0.98  
% 1.16/0.98  --qbf_mode                              false
% 1.16/0.98  --qbf_elim_univ                         false
% 1.16/0.98  --qbf_dom_inst                          none
% 1.16/0.98  --qbf_dom_pre_inst                      false
% 1.16/0.98  --qbf_sk_in                             false
% 1.16/0.98  --qbf_pred_elim                         true
% 1.16/0.98  --qbf_split                             512
% 1.16/0.98  
% 1.16/0.98  ------ BMC1 Options
% 1.16/0.98  
% 1.16/0.98  --bmc1_incremental                      false
% 1.16/0.98  --bmc1_axioms                           reachable_all
% 1.16/0.98  --bmc1_min_bound                        0
% 1.16/0.98  --bmc1_max_bound                        -1
% 1.16/0.98  --bmc1_max_bound_default                -1
% 1.16/0.98  --bmc1_symbol_reachability              true
% 1.16/0.98  --bmc1_property_lemmas                  false
% 1.16/0.98  --bmc1_k_induction                      false
% 1.16/0.98  --bmc1_non_equiv_states                 false
% 1.16/0.98  --bmc1_deadlock                         false
% 1.16/0.98  --bmc1_ucm                              false
% 1.16/0.98  --bmc1_add_unsat_core                   none
% 1.16/0.98  --bmc1_unsat_core_children              false
% 1.16/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.16/0.98  --bmc1_out_stat                         full
% 1.16/0.98  --bmc1_ground_init                      false
% 1.16/0.98  --bmc1_pre_inst_next_state              false
% 1.16/0.98  --bmc1_pre_inst_state                   false
% 1.16/0.98  --bmc1_pre_inst_reach_state             false
% 1.16/0.98  --bmc1_out_unsat_core                   false
% 1.16/0.98  --bmc1_aig_witness_out                  false
% 1.16/0.98  --bmc1_verbose                          false
% 1.16/0.98  --bmc1_dump_clauses_tptp                false
% 1.16/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.16/0.98  --bmc1_dump_file                        -
% 1.16/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.16/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.16/0.98  --bmc1_ucm_extend_mode                  1
% 1.16/0.98  --bmc1_ucm_init_mode                    2
% 1.16/0.98  --bmc1_ucm_cone_mode                    none
% 1.16/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.16/0.98  --bmc1_ucm_relax_model                  4
% 1.16/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.16/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.16/0.98  --bmc1_ucm_layered_model                none
% 1.16/0.98  --bmc1_ucm_max_lemma_size               10
% 1.16/0.98  
% 1.16/0.98  ------ AIG Options
% 1.16/0.98  
% 1.16/0.98  --aig_mode                              false
% 1.16/0.98  
% 1.16/0.98  ------ Instantiation Options
% 1.16/0.98  
% 1.16/0.98  --instantiation_flag                    true
% 1.16/0.98  --inst_sos_flag                         false
% 1.16/0.98  --inst_sos_phase                        true
% 1.16/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.16/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.16/0.98  --inst_lit_sel_side                     num_symb
% 1.16/0.98  --inst_solver_per_active                1400
% 1.16/0.98  --inst_solver_calls_frac                1.
% 1.16/0.98  --inst_passive_queue_type               priority_queues
% 1.16/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.16/0.98  --inst_passive_queues_freq              [25;2]
% 1.16/0.98  --inst_dismatching                      true
% 1.16/0.98  --inst_eager_unprocessed_to_passive     true
% 1.16/0.98  --inst_prop_sim_given                   true
% 1.16/0.98  --inst_prop_sim_new                     false
% 1.16/0.98  --inst_subs_new                         false
% 1.16/0.98  --inst_eq_res_simp                      false
% 1.16/0.98  --inst_subs_given                       false
% 1.16/0.98  --inst_orphan_elimination               true
% 1.16/0.98  --inst_learning_loop_flag               true
% 1.16/0.98  --inst_learning_start                   3000
% 1.16/0.98  --inst_learning_factor                  2
% 1.16/0.98  --inst_start_prop_sim_after_learn       3
% 1.16/0.98  --inst_sel_renew                        solver
% 1.16/0.98  --inst_lit_activity_flag                true
% 1.16/0.98  --inst_restr_to_given                   false
% 1.16/0.98  --inst_activity_threshold               500
% 1.16/0.98  --inst_out_proof                        true
% 1.16/0.98  
% 1.16/0.98  ------ Resolution Options
% 1.16/0.98  
% 1.16/0.98  --resolution_flag                       true
% 1.16/0.98  --res_lit_sel                           adaptive
% 1.16/0.98  --res_lit_sel_side                      none
% 1.16/0.98  --res_ordering                          kbo
% 1.16/0.98  --res_to_prop_solver                    active
% 1.16/0.98  --res_prop_simpl_new                    false
% 1.16/0.98  --res_prop_simpl_given                  true
% 1.16/0.98  --res_passive_queue_type                priority_queues
% 1.16/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.16/0.98  --res_passive_queues_freq               [15;5]
% 1.16/0.98  --res_forward_subs                      full
% 1.16/0.98  --res_backward_subs                     full
% 1.16/0.98  --res_forward_subs_resolution           true
% 1.16/0.98  --res_backward_subs_resolution          true
% 1.16/0.98  --res_orphan_elimination                true
% 1.16/0.98  --res_time_limit                        2.
% 1.16/0.98  --res_out_proof                         true
% 1.16/0.98  
% 1.16/0.98  ------ Superposition Options
% 1.16/0.98  
% 1.16/0.98  --superposition_flag                    true
% 1.16/0.98  --sup_passive_queue_type                priority_queues
% 1.16/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.16/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.16/0.98  --demod_completeness_check              fast
% 1.16/0.98  --demod_use_ground                      true
% 1.16/0.98  --sup_to_prop_solver                    passive
% 1.16/0.98  --sup_prop_simpl_new                    true
% 1.16/0.98  --sup_prop_simpl_given                  true
% 1.16/0.98  --sup_fun_splitting                     false
% 1.16/0.98  --sup_smt_interval                      50000
% 1.16/0.98  
% 1.16/0.98  ------ Superposition Simplification Setup
% 1.16/0.98  
% 1.16/0.98  --sup_indices_passive                   []
% 1.16/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.16/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/0.98  --sup_full_bw                           [BwDemod]
% 1.16/0.98  --sup_immed_triv                        [TrivRules]
% 1.16/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.16/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/0.98  --sup_immed_bw_main                     []
% 1.16/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.16/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.16/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.16/0.98  
% 1.16/0.98  ------ Combination Options
% 1.16/0.98  
% 1.16/0.98  --comb_res_mult                         3
% 1.16/0.98  --comb_sup_mult                         2
% 1.16/0.98  --comb_inst_mult                        10
% 1.16/0.98  
% 1.16/0.98  ------ Debug Options
% 1.16/0.98  
% 1.16/0.98  --dbg_backtrace                         false
% 1.16/0.98  --dbg_dump_prop_clauses                 false
% 1.16/0.98  --dbg_dump_prop_clauses_file            -
% 1.16/0.98  --dbg_out_stat                          false
% 1.16/0.98  ------ Parsing...
% 1.16/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.16/0.98  
% 1.16/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.16/0.98  
% 1.16/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.16/0.98  
% 1.16/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.16/0.98  ------ Proving...
% 1.16/0.98  ------ Problem Properties 
% 1.16/0.98  
% 1.16/0.98  
% 1.16/0.98  clauses                                 8
% 1.16/0.98  conjectures                             0
% 1.16/0.98  EPR                                     2
% 1.16/0.98  Horn                                    7
% 1.16/0.98  unary                                   2
% 1.16/0.98  binary                                  5
% 1.16/0.98  lits                                    15
% 1.16/0.98  lits eq                                 5
% 1.16/0.98  fd_pure                                 0
% 1.16/0.98  fd_pseudo                               0
% 1.16/0.98  fd_cond                                 0
% 1.16/0.98  fd_pseudo_cond                          1
% 1.16/0.98  AC symbols                              0
% 1.16/0.98  
% 1.16/0.98  ------ Schedule dynamic 5 is on 
% 1.16/0.98  
% 1.16/0.98  ------ no conjectures: strip conj schedule 
% 1.16/0.98  
% 1.16/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.16/0.98  
% 1.16/0.98  
% 1.16/0.98  ------ 
% 1.16/0.98  Current options:
% 1.16/0.98  ------ 
% 1.16/0.98  
% 1.16/0.98  ------ Input Options
% 1.16/0.98  
% 1.16/0.98  --out_options                           all
% 1.16/0.98  --tptp_safe_out                         true
% 1.16/0.98  --problem_path                          ""
% 1.16/0.98  --include_path                          ""
% 1.16/0.98  --clausifier                            res/vclausify_rel
% 1.16/0.98  --clausifier_options                    --mode clausify
% 1.16/0.98  --stdin                                 false
% 1.16/0.98  --stats_out                             all
% 1.16/0.98  
% 1.16/0.98  ------ General Options
% 1.16/0.98  
% 1.16/0.98  --fof                                   false
% 1.16/0.98  --time_out_real                         305.
% 1.16/0.98  --time_out_virtual                      -1.
% 1.16/0.98  --symbol_type_check                     false
% 1.16/0.98  --clausify_out                          false
% 1.16/0.98  --sig_cnt_out                           false
% 1.16/0.98  --trig_cnt_out                          false
% 1.16/0.98  --trig_cnt_out_tolerance                1.
% 1.16/0.98  --trig_cnt_out_sk_spl                   false
% 1.16/0.98  --abstr_cl_out                          false
% 1.16/0.98  
% 1.16/0.98  ------ Global Options
% 1.16/0.98  
% 1.16/0.98  --schedule                              default
% 1.16/0.98  --add_important_lit                     false
% 1.16/0.98  --prop_solver_per_cl                    1000
% 1.16/0.98  --min_unsat_core                        false
% 1.16/0.98  --soft_assumptions                      false
% 1.16/0.98  --soft_lemma_size                       3
% 1.16/0.98  --prop_impl_unit_size                   0
% 1.16/0.98  --prop_impl_unit                        []
% 1.16/0.98  --share_sel_clauses                     true
% 1.16/0.98  --reset_solvers                         false
% 1.16/0.98  --bc_imp_inh                            [conj_cone]
% 1.16/0.98  --conj_cone_tolerance                   3.
% 1.16/0.98  --extra_neg_conj                        none
% 1.16/0.98  --large_theory_mode                     true
% 1.16/0.98  --prolific_symb_bound                   200
% 1.16/0.98  --lt_threshold                          2000
% 1.16/0.98  --clause_weak_htbl                      true
% 1.16/0.98  --gc_record_bc_elim                     false
% 1.16/0.98  
% 1.16/0.98  ------ Preprocessing Options
% 1.16/0.98  
% 1.16/0.98  --preprocessing_flag                    true
% 1.16/0.98  --time_out_prep_mult                    0.1
% 1.16/0.98  --splitting_mode                        input
% 1.16/0.98  --splitting_grd                         true
% 1.16/0.98  --splitting_cvd                         false
% 1.16/0.98  --splitting_cvd_svl                     false
% 1.16/0.98  --splitting_nvd                         32
% 1.16/0.98  --sub_typing                            true
% 1.16/0.98  --prep_gs_sim                           true
% 1.16/0.98  --prep_unflatten                        true
% 1.16/0.98  --prep_res_sim                          true
% 1.16/0.98  --prep_upred                            true
% 1.16/0.98  --prep_sem_filter                       exhaustive
% 1.16/0.98  --prep_sem_filter_out                   false
% 1.16/0.98  --pred_elim                             true
% 1.16/0.98  --res_sim_input                         true
% 1.16/0.98  --eq_ax_congr_red                       true
% 1.16/0.98  --pure_diseq_elim                       true
% 1.16/0.98  --brand_transform                       false
% 1.16/0.98  --non_eq_to_eq                          false
% 1.16/0.98  --prep_def_merge                        true
% 1.16/0.98  --prep_def_merge_prop_impl              false
% 1.16/0.98  --prep_def_merge_mbd                    true
% 1.16/0.98  --prep_def_merge_tr_red                 false
% 1.16/0.98  --prep_def_merge_tr_cl                  false
% 1.16/0.98  --smt_preprocessing                     true
% 1.16/0.98  --smt_ac_axioms                         fast
% 1.16/0.98  --preprocessed_out                      false
% 1.16/0.98  --preprocessed_stats                    false
% 1.16/0.98  
% 1.16/0.98  ------ Abstraction refinement Options
% 1.16/0.98  
% 1.16/0.98  --abstr_ref                             []
% 1.16/0.98  --abstr_ref_prep                        false
% 1.16/0.98  --abstr_ref_until_sat                   false
% 1.16/0.98  --abstr_ref_sig_restrict                funpre
% 1.16/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.16/0.98  --abstr_ref_under                       []
% 1.16/0.98  
% 1.16/0.98  ------ SAT Options
% 1.16/0.98  
% 1.16/0.98  --sat_mode                              false
% 1.16/0.98  --sat_fm_restart_options                ""
% 1.16/0.98  --sat_gr_def                            false
% 1.16/0.98  --sat_epr_types                         true
% 1.16/0.98  --sat_non_cyclic_types                  false
% 1.16/0.98  --sat_finite_models                     false
% 1.16/0.98  --sat_fm_lemmas                         false
% 1.16/0.98  --sat_fm_prep                           false
% 1.16/0.98  --sat_fm_uc_incr                        true
% 1.16/0.98  --sat_out_model                         small
% 1.16/0.98  --sat_out_clauses                       false
% 1.16/0.98  
% 1.16/0.98  ------ QBF Options
% 1.16/0.98  
% 1.16/0.98  --qbf_mode                              false
% 1.16/0.98  --qbf_elim_univ                         false
% 1.16/0.98  --qbf_dom_inst                          none
% 1.16/0.98  --qbf_dom_pre_inst                      false
% 1.16/0.98  --qbf_sk_in                             false
% 1.16/0.98  --qbf_pred_elim                         true
% 1.16/0.98  --qbf_split                             512
% 1.16/0.98  
% 1.16/0.98  ------ BMC1 Options
% 1.16/0.98  
% 1.16/0.98  --bmc1_incremental                      false
% 1.16/0.98  --bmc1_axioms                           reachable_all
% 1.16/0.98  --bmc1_min_bound                        0
% 1.16/0.98  --bmc1_max_bound                        -1
% 1.16/0.98  --bmc1_max_bound_default                -1
% 1.16/0.98  --bmc1_symbol_reachability              true
% 1.16/0.98  --bmc1_property_lemmas                  false
% 1.16/0.98  --bmc1_k_induction                      false
% 1.16/0.98  --bmc1_non_equiv_states                 false
% 1.16/0.98  --bmc1_deadlock                         false
% 1.16/0.98  --bmc1_ucm                              false
% 1.16/0.98  --bmc1_add_unsat_core                   none
% 1.16/0.98  --bmc1_unsat_core_children              false
% 1.16/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.16/0.98  --bmc1_out_stat                         full
% 1.16/0.98  --bmc1_ground_init                      false
% 1.16/0.98  --bmc1_pre_inst_next_state              false
% 1.16/0.98  --bmc1_pre_inst_state                   false
% 1.16/0.98  --bmc1_pre_inst_reach_state             false
% 1.16/0.98  --bmc1_out_unsat_core                   false
% 1.16/0.98  --bmc1_aig_witness_out                  false
% 1.16/0.98  --bmc1_verbose                          false
% 1.16/0.98  --bmc1_dump_clauses_tptp                false
% 1.16/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.16/0.98  --bmc1_dump_file                        -
% 1.16/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.16/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.16/0.98  --bmc1_ucm_extend_mode                  1
% 1.16/0.98  --bmc1_ucm_init_mode                    2
% 1.16/0.98  --bmc1_ucm_cone_mode                    none
% 1.16/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.16/0.98  --bmc1_ucm_relax_model                  4
% 1.16/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.16/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.16/0.98  --bmc1_ucm_layered_model                none
% 1.16/0.98  --bmc1_ucm_max_lemma_size               10
% 1.16/0.98  
% 1.16/0.98  ------ AIG Options
% 1.16/0.98  
% 1.16/0.98  --aig_mode                              false
% 1.16/0.98  
% 1.16/0.98  ------ Instantiation Options
% 1.16/0.98  
% 1.16/0.98  --instantiation_flag                    true
% 1.16/0.98  --inst_sos_flag                         false
% 1.16/0.98  --inst_sos_phase                        true
% 1.16/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.16/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.16/0.98  --inst_lit_sel_side                     none
% 1.16/0.98  --inst_solver_per_active                1400
% 1.16/0.98  --inst_solver_calls_frac                1.
% 1.16/0.98  --inst_passive_queue_type               priority_queues
% 1.16/0.98  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.16/0.98  --inst_passive_queues_freq              [25;2]
% 1.16/0.98  --inst_dismatching                      true
% 1.16/0.98  --inst_eager_unprocessed_to_passive     true
% 1.16/0.98  --inst_prop_sim_given                   true
% 1.16/0.98  --inst_prop_sim_new                     false
% 1.16/0.98  --inst_subs_new                         false
% 1.16/0.98  --inst_eq_res_simp                      false
% 1.16/0.98  --inst_subs_given                       false
% 1.16/0.98  --inst_orphan_elimination               true
% 1.16/0.98  --inst_learning_loop_flag               true
% 1.16/0.98  --inst_learning_start                   3000
% 1.16/0.98  --inst_learning_factor                  2
% 1.16/0.98  --inst_start_prop_sim_after_learn       3
% 1.16/0.98  --inst_sel_renew                        solver
% 1.16/0.98  --inst_lit_activity_flag                true
% 1.16/0.98  --inst_restr_to_given                   false
% 1.16/0.98  --inst_activity_threshold               500
% 1.16/0.98  --inst_out_proof                        true
% 1.16/0.98  
% 1.16/0.98  ------ Resolution Options
% 1.16/0.98  
% 1.16/0.98  --resolution_flag                       false
% 1.16/0.98  --res_lit_sel                           adaptive
% 1.16/0.98  --res_lit_sel_side                      none
% 1.16/0.98  --res_ordering                          kbo
% 1.16/0.98  --res_to_prop_solver                    active
% 1.16/0.98  --res_prop_simpl_new                    false
% 1.16/0.98  --res_prop_simpl_given                  true
% 1.16/0.98  --res_passive_queue_type                priority_queues
% 1.16/0.98  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.16/0.98  --res_passive_queues_freq               [15;5]
% 1.16/0.98  --res_forward_subs                      full
% 1.16/0.98  --res_backward_subs                     full
% 1.16/0.98  --res_forward_subs_resolution           true
% 1.16/0.98  --res_backward_subs_resolution          true
% 1.16/0.98  --res_orphan_elimination                true
% 1.16/0.98  --res_time_limit                        2.
% 1.16/0.98  --res_out_proof                         true
% 1.16/0.98  
% 1.16/0.98  ------ Superposition Options
% 1.16/0.98  
% 1.16/0.98  --superposition_flag                    true
% 1.16/0.98  --sup_passive_queue_type                priority_queues
% 1.16/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.16/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.16/0.98  --demod_completeness_check              fast
% 1.16/0.98  --demod_use_ground                      true
% 1.16/0.98  --sup_to_prop_solver                    passive
% 1.16/0.98  --sup_prop_simpl_new                    true
% 1.16/0.98  --sup_prop_simpl_given                  true
% 1.16/0.98  --sup_fun_splitting                     false
% 1.16/0.98  --sup_smt_interval                      50000
% 1.16/0.98  
% 1.16/0.98  ------ Superposition Simplification Setup
% 1.16/0.98  
% 1.16/0.98  --sup_indices_passive                   []
% 1.16/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.16/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.16/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/0.98  --sup_full_bw                           [BwDemod]
% 1.16/0.98  --sup_immed_triv                        [TrivRules]
% 1.16/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.16/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/0.98  --sup_immed_bw_main                     []
% 1.16/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.16/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.16/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.16/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.16/0.98  
% 1.16/0.98  ------ Combination Options
% 1.16/0.98  
% 1.16/0.98  --comb_res_mult                         3
% 1.16/0.98  --comb_sup_mult                         2
% 1.16/0.98  --comb_inst_mult                        10
% 1.16/0.98  
% 1.16/0.98  ------ Debug Options
% 1.16/0.98  
% 1.16/0.98  --dbg_backtrace                         false
% 1.16/0.98  --dbg_dump_prop_clauses                 false
% 1.16/0.98  --dbg_dump_prop_clauses_file            -
% 1.16/0.98  --dbg_out_stat                          false
% 1.16/0.98  
% 1.16/0.98  
% 1.16/0.98  
% 1.16/0.98  
% 1.16/0.98  ------ Proving...
% 1.16/0.98  
% 1.16/0.98  
% 1.16/0.98  % SZS status Theorem for theBenchmark.p
% 1.16/0.98  
% 1.16/0.98   Resolution empty clause
% 1.16/0.98  
% 1.16/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.16/0.98  
% 1.16/0.98  fof(f4,axiom,(
% 1.16/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.16/0.98  
% 1.16/0.98  fof(f18,plain,(
% 1.16/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.16/0.98    inference(nnf_transformation,[],[f4])).
% 1.16/0.98  
% 1.16/0.98  fof(f30,plain,(
% 1.16/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.16/0.98    inference(cnf_transformation,[],[f18])).
% 1.16/0.98  
% 1.16/0.98  fof(f8,conjecture,(
% 1.16/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.16/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.16/0.98  
% 1.16/0.98  fof(f9,negated_conjecture,(
% 1.16/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.16/0.98    inference(negated_conjecture,[],[f8])).
% 1.16/0.98  
% 1.16/0.98  fof(f15,plain,(
% 1.16/0.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.16/0.98    inference(ennf_transformation,[],[f9])).
% 1.16/0.98  
% 1.16/0.98  fof(f20,plain,(
% 1.16/0.98    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.16/0.98    inference(nnf_transformation,[],[f15])).
% 1.16/0.98  
% 1.16/0.98  fof(f21,plain,(
% 1.16/0.98    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.16/0.98    inference(flattening,[],[f20])).
% 1.16/0.98  
% 1.16/0.98  fof(f23,plain,(
% 1.16/0.98    ( ! [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0) | ~v4_pre_topc(sK1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.16/0.99    introduced(choice_axiom,[])).
% 1.16/0.99  
% 1.16/0.99  fof(f22,plain,(
% 1.16/0.99    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.16/0.99    introduced(choice_axiom,[])).
% 1.16/0.99  
% 1.16/0.99  fof(f24,plain,(
% 1.16/0.99    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 1.16/0.99  
% 1.16/0.99  fof(f37,plain,(
% 1.16/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.16/0.99    inference(cnf_transformation,[],[f24])).
% 1.16/0.99  
% 1.16/0.99  fof(f7,axiom,(
% 1.16/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.16/0.99  
% 1.16/0.99  fof(f14,plain,(
% 1.16/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.16/0.99    inference(ennf_transformation,[],[f7])).
% 1.16/0.99  
% 1.16/0.99  fof(f35,plain,(
% 1.16/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.16/0.99    inference(cnf_transformation,[],[f14])).
% 1.16/0.99  
% 1.16/0.99  fof(f5,axiom,(
% 1.16/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.16/0.99  
% 1.16/0.99  fof(f12,plain,(
% 1.16/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.16/0.99    inference(ennf_transformation,[],[f5])).
% 1.16/0.99  
% 1.16/0.99  fof(f32,plain,(
% 1.16/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.16/0.99    inference(cnf_transformation,[],[f12])).
% 1.16/0.99  
% 1.16/0.99  fof(f36,plain,(
% 1.16/0.99    l1_pre_topc(sK0)),
% 1.16/0.99    inference(cnf_transformation,[],[f24])).
% 1.16/0.99  
% 1.16/0.99  fof(f2,axiom,(
% 1.16/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.16/0.99  
% 1.16/0.99  fof(f10,plain,(
% 1.16/0.99    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.99    inference(ennf_transformation,[],[f2])).
% 1.16/0.99  
% 1.16/0.99  fof(f28,plain,(
% 1.16/0.99    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.16/0.99    inference(cnf_transformation,[],[f10])).
% 1.16/0.99  
% 1.16/0.99  fof(f31,plain,(
% 1.16/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.16/0.99    inference(cnf_transformation,[],[f18])).
% 1.16/0.99  
% 1.16/0.99  fof(f1,axiom,(
% 1.16/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.16/0.99  
% 1.16/0.99  fof(f16,plain,(
% 1.16/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.16/0.99    inference(nnf_transformation,[],[f1])).
% 1.16/0.99  
% 1.16/0.99  fof(f17,plain,(
% 1.16/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.16/0.99    inference(flattening,[],[f16])).
% 1.16/0.99  
% 1.16/0.99  fof(f25,plain,(
% 1.16/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.16/0.99    inference(cnf_transformation,[],[f17])).
% 1.16/0.99  
% 1.16/0.99  fof(f41,plain,(
% 1.16/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.16/0.99    inference(equality_resolution,[],[f25])).
% 1.16/0.99  
% 1.16/0.99  fof(f3,axiom,(
% 1.16/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.16/0.99  
% 1.16/0.99  fof(f11,plain,(
% 1.16/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.99    inference(ennf_transformation,[],[f3])).
% 1.16/0.99  
% 1.16/0.99  fof(f29,plain,(
% 1.16/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.16/0.99    inference(cnf_transformation,[],[f11])).
% 1.16/0.99  
% 1.16/0.99  fof(f38,plain,(
% 1.16/0.99    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 1.16/0.99    inference(cnf_transformation,[],[f24])).
% 1.16/0.99  
% 1.16/0.99  fof(f6,axiom,(
% 1.16/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 1.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.16/0.99  
% 1.16/0.99  fof(f13,plain,(
% 1.16/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.16/0.99    inference(ennf_transformation,[],[f6])).
% 1.16/0.99  
% 1.16/0.99  fof(f19,plain,(
% 1.16/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.16/0.99    inference(nnf_transformation,[],[f13])).
% 1.16/0.99  
% 1.16/0.99  fof(f33,plain,(
% 1.16/0.99    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.16/0.99    inference(cnf_transformation,[],[f19])).
% 1.16/0.99  
% 1.16/0.99  fof(f39,plain,(
% 1.16/0.99    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.16/0.99    inference(cnf_transformation,[],[f24])).
% 1.16/0.99  
% 1.16/0.99  fof(f34,plain,(
% 1.16/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.16/0.99    inference(cnf_transformation,[],[f19])).
% 1.16/0.99  
% 1.16/0.99  cnf(c_6,plain,
% 1.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.16/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_117,plain,
% 1.16/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.16/0.99      inference(prop_impl,[status(thm)],[c_6]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_118,plain,
% 1.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.16/0.99      inference(renaming,[status(thm)],[c_117]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_13,negated_conjecture,
% 1.16/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.16/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_307,plain,
% 1.16/0.99      ( r1_tarski(X0,X1)
% 1.16/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
% 1.16/0.99      | sK1 != X0 ),
% 1.16/0.99      inference(resolution_lifted,[status(thm)],[c_118,c_13]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_308,plain,
% 1.16/0.99      ( r1_tarski(sK1,X0) | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 1.16/0.99      inference(unflattening,[status(thm)],[c_307]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_622,plain,
% 1.16/0.99      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
% 1.16/0.99      | r1_tarski(sK1,X0) = iProver_top ),
% 1.16/0.99      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_10,plain,
% 1.16/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.16/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_7,plain,
% 1.16/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.16/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_212,plain,
% 1.16/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.16/0.99      inference(resolution,[status(thm)],[c_10,c_7]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_14,negated_conjecture,
% 1.16/0.99      ( l1_pre_topc(sK0) ),
% 1.16/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_226,plain,
% 1.16/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.16/0.99      inference(resolution_lifted,[status(thm)],[c_212,c_14]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_227,plain,
% 1.16/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.16/0.99      inference(unflattening,[status(thm)],[c_226]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_633,plain,
% 1.16/0.99      ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0)
% 1.16/0.99      | r1_tarski(sK1,X0) = iProver_top ),
% 1.16/0.99      inference(light_normalisation,[status(thm)],[c_622,c_227]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_695,plain,
% 1.16/0.99      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 1.16/0.99      inference(equality_resolution,[status(thm)],[c_633]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_3,plain,
% 1.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.16/0.99      | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 1.16/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_5,plain,
% 1.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.16/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_119,plain,
% 1.16/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.16/0.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_120,plain,
% 1.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.16/0.99      inference(renaming,[status(thm)],[c_119]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_149,plain,
% 1.16/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 1.16/0.99      inference(bin_hyper_res,[status(thm)],[c_3,c_120]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_626,plain,
% 1.16/0.99      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
% 1.16/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 1.16/0.99      inference(predicate_to_equality,[status(thm)],[c_149]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_863,plain,
% 1.16/0.99      ( k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
% 1.16/0.99      inference(superposition,[status(thm)],[c_695,c_626]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f41]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_627,plain,
% 1.16/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 1.16/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_4,plain,
% 1.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.16/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 1.16/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_150,plain,
% 1.16/0.99      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 1.16/0.99      inference(bin_hyper_res,[status(thm)],[c_4,c_120]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_625,plain,
% 1.16/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 1.16/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 1.16/0.99      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_995,plain,
% 1.16/0.99      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 1.16/0.99      inference(superposition,[status(thm)],[c_627,c_625]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_12,negated_conjecture,
% 1.16/0.99      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | v4_pre_topc(sK1,sK0) ),
% 1.16/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_123,plain,
% 1.16/0.99      ( v4_pre_topc(sK1,sK0)
% 1.16/0.99      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 1.16/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_124,plain,
% 1.16/0.99      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | v4_pre_topc(sK1,sK0) ),
% 1.16/0.99      inference(renaming,[status(thm)],[c_123]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_9,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 1.16/0.99      | ~ v4_pre_topc(X1,X0)
% 1.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.16/0.99      | ~ l1_pre_topc(X0) ),
% 1.16/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_231,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 1.16/0.99      | ~ v4_pre_topc(X1,X0)
% 1.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.16/0.99      | sK0 != X0 ),
% 1.16/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_232,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
% 1.16/0.99      | ~ v4_pre_topc(X0,sK0)
% 1.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.16/0.99      inference(unflattening,[status(thm)],[c_231]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_272,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
% 1.16/0.99      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.16/0.99      | sK1 != X0
% 1.16/0.99      | sK0 != sK0 ),
% 1.16/0.99      inference(resolution_lifted,[status(thm)],[c_124,c_232]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_273,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.16/0.99      inference(unflattening,[status(thm)],[c_272]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_350,plain,
% 1.16/0.99      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
% 1.16/0.99      inference(prop_impl,[status(thm)],[c_13,c_273]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_351,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 1.16/0.99      inference(renaming,[status(thm)],[c_350]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_624,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
% 1.16/0.99      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
% 1.16/0.99      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_652,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
% 1.16/0.99      | v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 1.16/0.99      inference(light_normalisation,[status(thm)],[c_624,c_227]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_1004,plain,
% 1.16/0.99      ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 1.16/0.99      | v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 1.16/0.99      inference(demodulation,[status(thm)],[c_995,c_652]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_1151,plain,
% 1.16/0.99      ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 1.16/0.99      inference(demodulation,[status(thm)],[c_863,c_1004]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_11,negated_conjecture,
% 1.16/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ v4_pre_topc(sK1,sK0) ),
% 1.16/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_121,plain,
% 1.16/0.99      ( ~ v4_pre_topc(sK1,sK0)
% 1.16/0.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 1.16/0.99      inference(prop_impl,[status(thm)],[c_11]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_122,plain,
% 1.16/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ v4_pre_topc(sK1,sK0) ),
% 1.16/0.99      inference(renaming,[status(thm)],[c_121]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_8,plain,
% 1.16/0.99      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 1.16/0.99      | v4_pre_topc(X1,X0)
% 1.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.16/0.99      | ~ l1_pre_topc(X0) ),
% 1.16/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_246,plain,
% 1.16/0.99      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 1.16/0.99      | v4_pre_topc(X1,X0)
% 1.16/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.16/0.99      | sK0 != X0 ),
% 1.16/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_247,plain,
% 1.16/0.99      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
% 1.16/0.99      | v4_pre_topc(X0,sK0)
% 1.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.16/0.99      inference(unflattening,[status(thm)],[c_246]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_286,plain,
% 1.16/0.99      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
% 1.16/0.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.16/0.99      | sK1 != X0
% 1.16/0.99      | sK0 != sK0 ),
% 1.16/0.99      inference(resolution_lifted,[status(thm)],[c_122,c_247]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_287,plain,
% 1.16/0.99      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.16/0.99      inference(unflattening,[status(thm)],[c_286]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_348,plain,
% 1.16/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
% 1.16/0.99      inference(prop_impl,[status(thm)],[c_13,c_287]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_349,plain,
% 1.16/0.99      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
% 1.16/0.99      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 1.16/0.99      inference(renaming,[status(thm)],[c_348]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_623,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 1.16/0.99      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) != iProver_top ),
% 1.16/0.99      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_657,plain,
% 1.16/0.99      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 1.16/0.99      | v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 1.16/0.99      inference(light_normalisation,[status(thm)],[c_623,c_227]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_1005,plain,
% 1.16/0.99      ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
% 1.16/0.99      | v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 1.16/0.99      inference(demodulation,[status(thm)],[c_995,c_657]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_1152,plain,
% 1.16/0.99      ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 1.16/0.99      inference(demodulation,[status(thm)],[c_863,c_1005]) ).
% 1.16/0.99  
% 1.16/0.99  cnf(c_1156,plain,
% 1.16/0.99      ( $false ),
% 1.16/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1151,c_1152]) ).
% 1.16/0.99  
% 1.16/0.99  
% 1.16/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.16/0.99  
% 1.16/0.99  ------                               Statistics
% 1.16/0.99  
% 1.16/0.99  ------ General
% 1.16/0.99  
% 1.16/0.99  abstr_ref_over_cycles:                  0
% 1.16/0.99  abstr_ref_under_cycles:                 0
% 1.16/0.99  gc_basic_clause_elim:                   0
% 1.16/0.99  forced_gc_time:                         0
% 1.16/0.99  parsing_time:                           0.007
% 1.16/0.99  unif_index_cands_time:                  0.
% 1.16/0.99  unif_index_add_time:                    0.
% 1.16/0.99  orderings_time:                         0.
% 1.16/0.99  out_proof_time:                         0.008
% 1.16/0.99  total_time:                             0.07
% 1.16/0.99  num_of_symbols:                         45
% 1.16/0.99  num_of_terms:                           825
% 1.16/0.99  
% 1.16/0.99  ------ Preprocessing
% 1.16/0.99  
% 1.16/0.99  num_of_splits:                          0
% 1.16/0.99  num_of_split_atoms:                     0
% 1.16/0.99  num_of_reused_defs:                     0
% 1.16/0.99  num_eq_ax_congr_red:                    13
% 1.16/0.99  num_of_sem_filtered_clauses:            1
% 1.16/0.99  num_of_subtypes:                        0
% 1.16/0.99  monotx_restored_types:                  0
% 1.16/0.99  sat_num_of_epr_types:                   0
% 1.16/0.99  sat_num_of_non_cyclic_types:            0
% 1.16/0.99  sat_guarded_non_collapsed_types:        0
% 1.16/0.99  num_pure_diseq_elim:                    0
% 1.16/0.99  simp_replaced_by:                       0
% 1.16/0.99  res_preprocessed:                       57
% 1.16/0.99  prep_upred:                             0
% 1.16/0.99  prep_unflattend:                        6
% 1.16/0.99  smt_new_axioms:                         0
% 1.16/0.99  pred_elim_cands:                        2
% 1.16/0.99  pred_elim:                              4
% 1.16/0.99  pred_elim_cl:                           6
% 1.16/0.99  pred_elim_cycles:                       6
% 1.16/0.99  merged_defs:                            10
% 1.16/0.99  merged_defs_ncl:                        0
% 1.16/0.99  bin_hyper_res:                          12
% 1.16/0.99  prep_cycles:                            4
% 1.16/0.99  pred_elim_time:                         0.002
% 1.16/0.99  splitting_time:                         0.
% 1.16/0.99  sem_filter_time:                        0.
% 1.16/0.99  monotx_time:                            0.
% 1.16/0.99  subtype_inf_time:                       0.
% 1.16/0.99  
% 1.16/0.99  ------ Problem properties
% 1.16/0.99  
% 1.16/0.99  clauses:                                8
% 1.16/0.99  conjectures:                            0
% 1.16/0.99  epr:                                    2
% 1.16/0.99  horn:                                   7
% 1.16/0.99  ground:                                 3
% 1.16/0.99  unary:                                  2
% 1.16/0.99  binary:                                 5
% 1.16/0.99  lits:                                   15
% 1.16/0.99  lits_eq:                                5
% 1.16/0.99  fd_pure:                                0
% 1.16/0.99  fd_pseudo:                              0
% 1.16/0.99  fd_cond:                                0
% 1.16/0.99  fd_pseudo_cond:                         1
% 1.16/0.99  ac_symbols:                             0
% 1.16/0.99  
% 1.16/0.99  ------ Propositional Solver
% 1.16/0.99  
% 1.16/0.99  prop_solver_calls:                      26
% 1.16/0.99  prop_fast_solver_calls:                 295
% 1.16/0.99  smt_solver_calls:                       0
% 1.16/0.99  smt_fast_solver_calls:                  0
% 1.16/0.99  prop_num_of_clauses:                    342
% 1.16/0.99  prop_preprocess_simplified:             1772
% 1.16/0.99  prop_fo_subsumed:                       2
% 1.16/0.99  prop_solver_time:                       0.
% 1.16/0.99  smt_solver_time:                        0.
% 1.16/0.99  smt_fast_solver_time:                   0.
% 1.16/0.99  prop_fast_solver_time:                  0.
% 1.16/0.99  prop_unsat_core_time:                   0.
% 1.16/0.99  
% 1.16/0.99  ------ QBF
% 1.16/0.99  
% 1.16/0.99  qbf_q_res:                              0
% 1.16/0.99  qbf_num_tautologies:                    0
% 1.16/0.99  qbf_prep_cycles:                        0
% 1.16/0.99  
% 1.16/0.99  ------ BMC1
% 1.16/0.99  
% 1.16/0.99  bmc1_current_bound:                     -1
% 1.16/0.99  bmc1_last_solved_bound:                 -1
% 1.16/0.99  bmc1_unsat_core_size:                   -1
% 1.16/0.99  bmc1_unsat_core_parents_size:           -1
% 1.16/0.99  bmc1_merge_next_fun:                    0
% 1.16/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.16/0.99  
% 1.16/0.99  ------ Instantiation
% 1.16/0.99  
% 1.16/0.99  inst_num_of_clauses:                    118
% 1.16/0.99  inst_num_in_passive:                    12
% 1.16/0.99  inst_num_in_active:                     75
% 1.16/0.99  inst_num_in_unprocessed:                31
% 1.16/0.99  inst_num_of_loops:                      80
% 1.16/0.99  inst_num_of_learning_restarts:          0
% 1.16/0.99  inst_num_moves_active_passive:          3
% 1.16/0.99  inst_lit_activity:                      0
% 1.16/0.99  inst_lit_activity_moves:                0
% 1.16/0.99  inst_num_tautologies:                   0
% 1.16/0.99  inst_num_prop_implied:                  0
% 1.16/0.99  inst_num_existing_simplified:           0
% 1.16/0.99  inst_num_eq_res_simplified:             0
% 1.16/0.99  inst_num_child_elim:                    0
% 1.16/0.99  inst_num_of_dismatching_blockings:      3
% 1.16/0.99  inst_num_of_non_proper_insts:           108
% 1.16/0.99  inst_num_of_duplicates:                 0
% 1.16/0.99  inst_inst_num_from_inst_to_res:         0
% 1.16/0.99  inst_dismatching_checking_time:         0.
% 1.16/0.99  
% 1.16/0.99  ------ Resolution
% 1.16/0.99  
% 1.16/0.99  res_num_of_clauses:                     0
% 1.16/0.99  res_num_in_passive:                     0
% 1.16/0.99  res_num_in_active:                      0
% 1.16/0.99  res_num_of_loops:                       61
% 1.16/0.99  res_forward_subset_subsumed:            41
% 1.16/0.99  res_backward_subset_subsumed:           0
% 1.16/0.99  res_forward_subsumed:                   0
% 1.16/0.99  res_backward_subsumed:                  0
% 1.16/0.99  res_forward_subsumption_resolution:     0
% 1.16/0.99  res_backward_subsumption_resolution:    0
% 1.16/0.99  res_clause_to_clause_subsumption:       38
% 1.16/0.99  res_orphan_elimination:                 0
% 1.16/0.99  res_tautology_del:                      31
% 1.16/0.99  res_num_eq_res_simplified:              0
% 1.16/0.99  res_num_sel_changes:                    0
% 1.16/0.99  res_moves_from_active_to_pass:          0
% 1.16/0.99  
% 1.16/0.99  ------ Superposition
% 1.16/0.99  
% 1.16/0.99  sup_time_total:                         0.
% 1.16/0.99  sup_time_generating:                    0.
% 1.16/0.99  sup_time_sim_full:                      0.
% 1.16/0.99  sup_time_sim_immed:                     0.
% 1.16/0.99  
% 1.16/0.99  sup_num_of_clauses:                     13
% 1.16/0.99  sup_num_in_active:                      10
% 1.16/0.99  sup_num_in_passive:                     3
% 1.16/0.99  sup_num_of_loops:                       14
% 1.16/0.99  sup_fw_superposition:                   6
% 1.16/0.99  sup_bw_superposition:                   1
% 1.16/0.99  sup_immediate_simplified:               0
% 1.16/0.99  sup_given_eliminated:                   0
% 1.16/0.99  comparisons_done:                       0
% 1.16/0.99  comparisons_avoided:                    0
% 1.16/0.99  
% 1.16/0.99  ------ Simplifications
% 1.16/0.99  
% 1.16/0.99  
% 1.16/0.99  sim_fw_subset_subsumed:                 0
% 1.16/0.99  sim_bw_subset_subsumed:                 0
% 1.16/0.99  sim_fw_subsumed:                        0
% 1.16/0.99  sim_bw_subsumed:                        0
% 1.16/0.99  sim_fw_subsumption_res:                 1
% 1.16/0.99  sim_bw_subsumption_res:                 0
% 1.16/0.99  sim_tautology_del:                      1
% 1.16/0.99  sim_eq_tautology_del:                   1
% 1.16/0.99  sim_eq_res_simp:                        0
% 1.16/0.99  sim_fw_demodulated:                     0
% 1.16/0.99  sim_bw_demodulated:                     4
% 1.16/0.99  sim_light_normalised:                   3
% 1.16/0.99  sim_joinable_taut:                      0
% 1.16/0.99  sim_joinable_simp:                      0
% 1.16/0.99  sim_ac_normalised:                      0
% 1.16/0.99  sim_smt_subsumption:                    0
% 1.16/0.99  
%------------------------------------------------------------------------------
