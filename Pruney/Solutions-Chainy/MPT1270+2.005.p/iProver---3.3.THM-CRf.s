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
% DateTime   : Thu Dec  3 12:15:15 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 470 expanded)
%              Number of clauses        :   77 ( 175 expanded)
%              Number of leaves         :   14 (  97 expanded)
%              Depth                    :   17
%              Number of atoms          :  307 (1644 expanded)
%              Number of equality atoms :  133 ( 316 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f54,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_783,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_779,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1450,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_779])).

cnf(c_17,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_770,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_782,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3698,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_770,c_782])).

cnf(c_4321,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(X0,k4_xboole_0(k2_tops_1(sK0,sK1),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_3698])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_780,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2481,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_780])).

cnf(c_4910,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4321,c_2481])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_781,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1451,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_779])).

cnf(c_1746,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1451])).

cnf(c_2477,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_780])).

cnf(c_3106,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2477])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_784,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3213,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3106,c_784])).

cnf(c_28873,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0)) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4910,c_3213])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_769,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_774,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3935,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_769,c_774])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_778,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1289,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_769,c_778])).

cnf(c_3938,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3935,c_1289])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4692,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3938,c_20])).

cnf(c_28908,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28873,c_6,c_4692])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_962,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_963,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | v2_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_965,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_28948,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28908,c_20,c_21,c_965])).

cnf(c_15,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_772,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3957,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_769,c_772])).

cnf(c_4216,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3957,c_20])).

cnf(c_4217,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4216])).

cnf(c_28953,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_28948,c_4217])).

cnf(c_4696,plain,
    ( r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4692,c_1450])).

cnf(c_8698,plain,
    ( r1_tarski(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_4696])).

cnf(c_29186,plain,
    ( r1_tarski(sK1,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28953,c_8698])).

cnf(c_1102,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,k2_tops_1(sK0,sK1)))
    | r1_tarski(k4_xboole_0(X0,X1),k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_15842,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)))
    | r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_15843,plain,
    ( r1_tarski(X0,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15842])).

cnf(c_15845,plain,
    ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15843])).

cnf(c_944,plain,
    ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1101,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),k2_tops_1(sK0,sK1))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_9388,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_tops_1(sK0,sK1))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_9389,plain,
    ( r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,k4_xboole_0(X0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9388])).

cnf(c_9391,plain,
    ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9389])).

cnf(c_342,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1442,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k4_xboole_0(X2,X3))
    | k4_xboole_0(X2,X3) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_3557,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k4_xboole_0(X1,k1_xboole_0))
    | k4_xboole_0(X1,k1_xboole_0) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_3558,plain,
    ( k4_xboole_0(X0,k1_xboole_0) != X0
    | sK1 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK1,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3557])).

cnf(c_3560,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != sK1
    | sK1 != sK1
    | r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3558])).

cnf(c_61,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_56,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_58,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_57,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_51,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29186,c_28948,c_15845,c_9391,c_3560,c_61,c_58,c_57,c_51,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:27:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.93/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.93/1.51  
% 7.93/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.93/1.51  
% 7.93/1.51  ------  iProver source info
% 7.93/1.51  
% 7.93/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.93/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.93/1.51  git: non_committed_changes: false
% 7.93/1.51  git: last_make_outside_of_git: false
% 7.93/1.51  
% 7.93/1.51  ------ 
% 7.93/1.51  ------ Parsing...
% 7.93/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.93/1.51  
% 7.93/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.93/1.51  
% 7.93/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.93/1.51  
% 7.93/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.93/1.51  ------ Proving...
% 7.93/1.51  ------ Problem Properties 
% 7.93/1.51  
% 7.93/1.51  
% 7.93/1.51  clauses                                 19
% 7.93/1.51  conjectures                             4
% 7.93/1.51  EPR                                     4
% 7.93/1.51  Horn                                    18
% 7.93/1.51  unary                                   6
% 7.93/1.51  binary                                  5
% 7.93/1.51  lits                                    42
% 7.93/1.51  lits eq                                 8
% 7.93/1.51  fd_pure                                 0
% 7.93/1.51  fd_pseudo                               0
% 7.93/1.51  fd_cond                                 0
% 7.93/1.51  fd_pseudo_cond                          1
% 7.93/1.51  AC symbols                              0
% 7.93/1.51  
% 7.93/1.51  ------ Input Options Time Limit: Unbounded
% 7.93/1.51  
% 7.93/1.51  
% 7.93/1.51  ------ 
% 7.93/1.51  Current options:
% 7.93/1.51  ------ 
% 7.93/1.51  
% 7.93/1.51  
% 7.93/1.51  
% 7.93/1.51  
% 7.93/1.51  ------ Proving...
% 7.93/1.51  
% 7.93/1.51  
% 7.93/1.51  % SZS status Theorem for theBenchmark.p
% 7.93/1.51  
% 7.93/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.93/1.51  
% 7.93/1.51  fof(f2,axiom,(
% 7.93/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f28,plain,(
% 7.93/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.93/1.51    inference(nnf_transformation,[],[f2])).
% 7.93/1.51  
% 7.93/1.51  fof(f29,plain,(
% 7.93/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.93/1.51    inference(flattening,[],[f28])).
% 7.93/1.51  
% 7.93/1.51  fof(f37,plain,(
% 7.93/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.93/1.51    inference(cnf_transformation,[],[f29])).
% 7.93/1.51  
% 7.93/1.51  fof(f57,plain,(
% 7.93/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.93/1.51    inference(equality_resolution,[],[f37])).
% 7.93/1.51  
% 7.93/1.51  fof(f7,axiom,(
% 7.93/1.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f19,plain,(
% 7.93/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.93/1.51    inference(ennf_transformation,[],[f7])).
% 7.93/1.51  
% 7.93/1.51  fof(f44,plain,(
% 7.93/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.93/1.51    inference(cnf_transformation,[],[f19])).
% 7.93/1.51  
% 7.93/1.51  fof(f14,conjecture,(
% 7.93/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f15,negated_conjecture,(
% 7.93/1.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 7.93/1.51    inference(negated_conjecture,[],[f14])).
% 7.93/1.51  
% 7.93/1.51  fof(f27,plain,(
% 7.93/1.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.93/1.51    inference(ennf_transformation,[],[f15])).
% 7.93/1.51  
% 7.93/1.51  fof(f31,plain,(
% 7.93/1.51    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.93/1.51    inference(nnf_transformation,[],[f27])).
% 7.93/1.51  
% 7.93/1.51  fof(f32,plain,(
% 7.93/1.51    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.93/1.51    inference(flattening,[],[f31])).
% 7.93/1.51  
% 7.93/1.51  fof(f34,plain,(
% 7.93/1.51    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.93/1.51    introduced(choice_axiom,[])).
% 7.93/1.51  
% 7.93/1.51  fof(f33,plain,(
% 7.93/1.51    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.93/1.51    introduced(choice_axiom,[])).
% 7.93/1.51  
% 7.93/1.51  fof(f35,plain,(
% 7.93/1.51    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.93/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 7.93/1.51  
% 7.93/1.51  fof(f54,plain,(
% 7.93/1.51    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 7.93/1.51    inference(cnf_transformation,[],[f35])).
% 7.93/1.51  
% 7.93/1.51  fof(f3,axiom,(
% 7.93/1.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f16,plain,(
% 7.93/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.93/1.51    inference(ennf_transformation,[],[f3])).
% 7.93/1.51  
% 7.93/1.51  fof(f17,plain,(
% 7.93/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.93/1.51    inference(flattening,[],[f16])).
% 7.93/1.51  
% 7.93/1.51  fof(f40,plain,(
% 7.93/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.93/1.51    inference(cnf_transformation,[],[f17])).
% 7.93/1.51  
% 7.93/1.51  fof(f1,axiom,(
% 7.93/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f36,plain,(
% 7.93/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.93/1.51    inference(cnf_transformation,[],[f1])).
% 7.93/1.51  
% 7.93/1.51  fof(f6,axiom,(
% 7.93/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f18,plain,(
% 7.93/1.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.93/1.51    inference(ennf_transformation,[],[f6])).
% 7.93/1.51  
% 7.93/1.51  fof(f43,plain,(
% 7.93/1.51    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.93/1.51    inference(cnf_transformation,[],[f18])).
% 7.93/1.51  
% 7.93/1.51  fof(f5,axiom,(
% 7.93/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f42,plain,(
% 7.93/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.93/1.51    inference(cnf_transformation,[],[f5])).
% 7.93/1.51  
% 7.93/1.51  fof(f4,axiom,(
% 7.93/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f41,plain,(
% 7.93/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.93/1.51    inference(cnf_transformation,[],[f4])).
% 7.93/1.51  
% 7.93/1.51  fof(f39,plain,(
% 7.93/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.93/1.51    inference(cnf_transformation,[],[f29])).
% 7.93/1.51  
% 7.93/1.51  fof(f53,plain,(
% 7.93/1.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.93/1.51    inference(cnf_transformation,[],[f35])).
% 7.93/1.51  
% 7.93/1.51  fof(f12,axiom,(
% 7.93/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f25,plain,(
% 7.93/1.51    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.51    inference(ennf_transformation,[],[f12])).
% 7.93/1.51  
% 7.93/1.51  fof(f49,plain,(
% 7.93/1.51    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.93/1.51    inference(cnf_transformation,[],[f25])).
% 7.93/1.51  
% 7.93/1.51  fof(f8,axiom,(
% 7.93/1.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f20,plain,(
% 7.93/1.51    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.93/1.51    inference(ennf_transformation,[],[f8])).
% 7.93/1.51  
% 7.93/1.51  fof(f45,plain,(
% 7.93/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.93/1.51    inference(cnf_transformation,[],[f20])).
% 7.93/1.51  
% 7.93/1.51  fof(f52,plain,(
% 7.93/1.51    l1_pre_topc(sK0)),
% 7.93/1.51    inference(cnf_transformation,[],[f35])).
% 7.93/1.51  
% 7.93/1.51  fof(f13,axiom,(
% 7.93/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 7.93/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.93/1.51  
% 7.93/1.51  fof(f26,plain,(
% 7.93/1.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.51    inference(ennf_transformation,[],[f13])).
% 7.93/1.51  
% 7.93/1.51  fof(f30,plain,(
% 7.93/1.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.93/1.51    inference(nnf_transformation,[],[f26])).
% 7.93/1.51  
% 7.93/1.51  fof(f51,plain,(
% 7.93/1.51    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.93/1.51    inference(cnf_transformation,[],[f30])).
% 7.93/1.51  
% 7.93/1.51  fof(f50,plain,(
% 7.93/1.51    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.93/1.51    inference(cnf_transformation,[],[f30])).
% 7.93/1.51  
% 7.93/1.51  fof(f55,plain,(
% 7.93/1.51    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 7.93/1.51    inference(cnf_transformation,[],[f35])).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3,plain,
% 7.93/1.51      ( r1_tarski(X0,X0) ),
% 7.93/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_783,plain,
% 7.93/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_8,plain,
% 7.93/1.51      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.93/1.51      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.93/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_779,plain,
% 7.93/1.51      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 7.93/1.51      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_1450,plain,
% 7.93/1.51      ( r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_783,c_779]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_17,negated_conjecture,
% 7.93/1.51      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 7.93/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_770,plain,
% 7.93/1.51      ( v2_tops_1(sK1,sK0) = iProver_top
% 7.93/1.51      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_4,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.93/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_782,plain,
% 7.93/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.93/1.51      | r1_tarski(X1,X2) != iProver_top
% 7.93/1.51      | r1_tarski(X0,X2) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3698,plain,
% 7.93/1.51      ( v2_tops_1(sK1,sK0) = iProver_top
% 7.93/1.51      | r1_tarski(k2_tops_1(sK0,sK1),X0) != iProver_top
% 7.93/1.51      | r1_tarski(sK1,X0) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_770,c_782]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_4321,plain,
% 7.93/1.51      ( v2_tops_1(sK1,sK0) = iProver_top
% 7.93/1.51      | r1_tarski(sK1,k2_xboole_0(X0,k4_xboole_0(k2_tops_1(sK0,sK1),X0))) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_1450,c_3698]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_0,plain,
% 7.93/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.93/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_7,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.93/1.51      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.93/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_780,plain,
% 7.93/1.51      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.93/1.51      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_2481,plain,
% 7.93/1.51      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.93/1.51      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_0,c_780]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_4910,plain,
% 7.93/1.51      ( v2_tops_1(sK1,sK0) = iProver_top
% 7.93/1.51      | r1_tarski(k4_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),X0)),X0) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_4321,c_2481]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_6,plain,
% 7.93/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.93/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_5,plain,
% 7.93/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.93/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_781,plain,
% 7.93/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_1451,plain,
% 7.93/1.51      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_781,c_779]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_1746,plain,
% 7.93/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_0,c_1451]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_2477,plain,
% 7.93/1.51      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_1746,c_780]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3106,plain,
% 7.93/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_6,c_2477]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_1,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.93/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_784,plain,
% 7.93/1.51      ( X0 = X1
% 7.93/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.93/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3213,plain,
% 7.93/1.51      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_3106,c_784]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_28873,plain,
% 7.93/1.51      ( k4_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0)) = k1_xboole_0
% 7.93/1.51      | v2_tops_1(sK1,sK0) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_4910,c_3213]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_18,negated_conjecture,
% 7.93/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.93/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_769,plain,
% 7.93/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_13,plain,
% 7.93/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.93/1.51      | ~ l1_pre_topc(X1)
% 7.93/1.51      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 7.93/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_774,plain,
% 7.93/1.51      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 7.93/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.93/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3935,plain,
% 7.93/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 7.93/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_769,c_774]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_9,plain,
% 7.93/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.93/1.51      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.93/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_778,plain,
% 7.93/1.51      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 7.93/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_1289,plain,
% 7.93/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_769,c_778]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3938,plain,
% 7.93/1.51      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 7.93/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.93/1.51      inference(demodulation,[status(thm)],[c_3935,c_1289]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_19,negated_conjecture,
% 7.93/1.51      ( l1_pre_topc(sK0) ),
% 7.93/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_20,plain,
% 7.93/1.51      ( l1_pre_topc(sK0) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_4692,plain,
% 7.93/1.51      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 7.93/1.51      inference(global_propositional_subsumption,
% 7.93/1.51                [status(thm)],
% 7.93/1.51                [c_3938,c_20]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_28908,plain,
% 7.93/1.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.93/1.51      | v2_tops_1(sK1,sK0) = iProver_top ),
% 7.93/1.51      inference(demodulation,[status(thm)],[c_28873,c_6,c_4692]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_21,plain,
% 7.93/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_14,plain,
% 7.93/1.51      ( v2_tops_1(X0,X1)
% 7.93/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.93/1.51      | ~ l1_pre_topc(X1)
% 7.93/1.51      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 7.93/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_962,plain,
% 7.93/1.51      ( v2_tops_1(X0,sK0)
% 7.93/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.93/1.51      | ~ l1_pre_topc(sK0)
% 7.93/1.51      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_963,plain,
% 7.93/1.51      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 7.93/1.51      | v2_tops_1(X0,sK0) = iProver_top
% 7.93/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.93/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_965,plain,
% 7.93/1.51      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 7.93/1.51      | v2_tops_1(sK1,sK0) = iProver_top
% 7.93/1.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.93/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_963]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_28948,plain,
% 7.93/1.51      ( v2_tops_1(sK1,sK0) = iProver_top ),
% 7.93/1.51      inference(global_propositional_subsumption,
% 7.93/1.51                [status(thm)],
% 7.93/1.51                [c_28908,c_20,c_21,c_965]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_15,plain,
% 7.93/1.51      ( ~ v2_tops_1(X0,X1)
% 7.93/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.93/1.51      | ~ l1_pre_topc(X1)
% 7.93/1.51      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 7.93/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_772,plain,
% 7.93/1.51      ( k1_tops_1(X0,X1) = k1_xboole_0
% 7.93/1.51      | v2_tops_1(X1,X0) != iProver_top
% 7.93/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.93/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3957,plain,
% 7.93/1.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.93/1.51      | v2_tops_1(sK1,sK0) != iProver_top
% 7.93/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_769,c_772]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_4216,plain,
% 7.93/1.51      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.93/1.51      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.93/1.51      inference(global_propositional_subsumption,
% 7.93/1.51                [status(thm)],
% 7.93/1.51                [c_3957,c_20]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_4217,plain,
% 7.93/1.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.93/1.51      | v2_tops_1(sK1,sK0) != iProver_top ),
% 7.93/1.51      inference(renaming,[status(thm)],[c_4216]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_28953,plain,
% 7.93/1.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_28948,c_4217]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_4696,plain,
% 7.93/1.51      ( r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_4692,c_1450]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_8698,plain,
% 7.93/1.51      ( r1_tarski(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = iProver_top ),
% 7.93/1.51      inference(superposition,[status(thm)],[c_0,c_4696]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_29186,plain,
% 7.93/1.51      ( r1_tarski(sK1,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) = iProver_top ),
% 7.93/1.51      inference(demodulation,[status(thm)],[c_28953,c_8698]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_1102,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,k2_xboole_0(X1,k2_tops_1(sK0,sK1)))
% 7.93/1.51      | r1_tarski(k4_xboole_0(X0,X1),k2_tops_1(sK0,sK1)) ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_15842,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)))
% 7.93/1.51      | r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_tops_1(sK0,sK1)) ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_1102]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_15843,plain,
% 7.93/1.51      ( r1_tarski(X0,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) != iProver_top
% 7.93/1.51      | r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_15842]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_15845,plain,
% 7.93/1.51      ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top
% 7.93/1.51      | r1_tarski(sK1,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) != iProver_top ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_15843]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_944,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
% 7.93/1.51      | ~ r1_tarski(sK1,X0)
% 7.93/1.51      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_1101,plain,
% 7.93/1.51      ( ~ r1_tarski(k4_xboole_0(X0,X1),k2_tops_1(sK0,sK1))
% 7.93/1.51      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 7.93/1.51      | ~ r1_tarski(sK1,k4_xboole_0(X0,X1)) ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_944]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_9388,plain,
% 7.93/1.51      ( ~ r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_tops_1(sK0,sK1))
% 7.93/1.51      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 7.93/1.51      | ~ r1_tarski(sK1,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_1101]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_9389,plain,
% 7.93/1.51      ( r1_tarski(k4_xboole_0(X0,k1_xboole_0),k2_tops_1(sK0,sK1)) != iProver_top
% 7.93/1.51      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
% 7.93/1.51      | r1_tarski(sK1,k4_xboole_0(X0,k1_xboole_0)) != iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_9388]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_9391,plain,
% 7.93/1.51      ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) != iProver_top
% 7.93/1.51      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top
% 7.93/1.51      | r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0)) != iProver_top ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_9389]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_342,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.93/1.51      theory(equality) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_1442,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,X1)
% 7.93/1.51      | r1_tarski(sK1,k4_xboole_0(X2,X3))
% 7.93/1.51      | k4_xboole_0(X2,X3) != X1
% 7.93/1.51      | sK1 != X0 ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_342]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3557,plain,
% 7.93/1.51      ( ~ r1_tarski(X0,X1)
% 7.93/1.51      | r1_tarski(sK1,k4_xboole_0(X1,k1_xboole_0))
% 7.93/1.51      | k4_xboole_0(X1,k1_xboole_0) != X1
% 7.93/1.51      | sK1 != X0 ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_1442]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3558,plain,
% 7.93/1.51      ( k4_xboole_0(X0,k1_xboole_0) != X0
% 7.93/1.51      | sK1 != X1
% 7.93/1.51      | r1_tarski(X1,X0) != iProver_top
% 7.93/1.51      | r1_tarski(sK1,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_3557]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_3560,plain,
% 7.93/1.51      ( k4_xboole_0(sK1,k1_xboole_0) != sK1
% 7.93/1.51      | sK1 != sK1
% 7.93/1.51      | r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0)) = iProver_top
% 7.93/1.51      | r1_tarski(sK1,sK1) != iProver_top ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_3558]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_61,plain,
% 7.93/1.51      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_56,plain,
% 7.93/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_58,plain,
% 7.93/1.51      ( r1_tarski(sK1,sK1) = iProver_top ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_56]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_57,plain,
% 7.93/1.51      ( r1_tarski(sK1,sK1) ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_51,plain,
% 7.93/1.51      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 7.93/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_16,negated_conjecture,
% 7.93/1.51      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 7.93/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(c_23,plain,
% 7.93/1.51      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.93/1.51      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 7.93/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.93/1.51  
% 7.93/1.51  cnf(contradiction,plain,
% 7.93/1.51      ( $false ),
% 7.93/1.51      inference(minisat,
% 7.93/1.51                [status(thm)],
% 7.93/1.51                [c_29186,c_28948,c_15845,c_9391,c_3560,c_61,c_58,c_57,
% 7.93/1.51                 c_51,c_23]) ).
% 7.93/1.51  
% 7.93/1.51  
% 7.93/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.93/1.51  
% 7.93/1.51  ------                               Statistics
% 7.93/1.51  
% 7.93/1.51  ------ Selected
% 7.93/1.51  
% 7.93/1.51  total_time:                             0.824
% 7.93/1.51  
%------------------------------------------------------------------------------
