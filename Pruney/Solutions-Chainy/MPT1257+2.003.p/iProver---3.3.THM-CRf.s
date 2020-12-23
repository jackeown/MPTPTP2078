%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:13 EST 2020

% Result     : Theorem 19.89s
% Output     : CNFRefutation 19.89s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 828 expanded)
%              Number of clauses        :   82 ( 313 expanded)
%              Number of leaves         :   14 ( 198 expanded)
%              Depth                    :   24
%              Number of atoms          :  327 (2271 expanded)
%              Number of equality atoms :  143 ( 410 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_xboole_0(k1_tops_1(X0,sK1),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f32,f31])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_146,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_453,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_441,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k4_subset_1(u1_struct_0(X0_42),X0_43,k2_tops_1(X0_42,X0_43)) = k2_pre_topc(X0_42,X0_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_451,plain,
    ( k4_subset_1(u1_struct_0(X0_42),X0_43,k2_tops_1(X0_42,X0_43)) = k2_pre_topc(X0_42,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_2414,plain,
    ( k4_subset_1(u1_struct_0(X0_42),k3_subset_1(u1_struct_0(X0_42),X0_43),k2_tops_1(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_441,c_451])).

cnf(c_37821,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_2414])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_149,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k2_tops_1(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43)) = k2_tops_1(X0_42,X0_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_450,plain,
    ( k2_tops_1(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43)) = k2_tops_1(X0_42,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_1353,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_450])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_212,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_1390,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1353,c_14,c_13,c_212])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_150,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_449,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_1393,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_449])).

cnf(c_15,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_208,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_210,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_3300,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1393,c_15,c_16,c_210])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
    | k4_subset_1(X0_45,X0_43,X1_43) = k4_subset_1(X0_45,X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_440,plain,
    ( k4_subset_1(X0_45,X0_43,X1_43) = k4_subset_1(X0_45,X1_43,X0_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_1016,plain,
    ( k4_subset_1(X0_45,k3_subset_1(X0_45,X0_43),X1_43) = k4_subset_1(X0_45,X1_43,k3_subset_1(X0_45,X0_43))
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(superposition,[status(thm)],[c_441,c_440])).

cnf(c_5210,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X0_43)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_43),k2_tops_1(sK0,sK1))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_1016])).

cnf(c_35928,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_453,c_5210])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_156,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
    | k4_subset_1(X0_45,X1_43,X0_43) = k2_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_443,plain,
    ( k4_subset_1(X0_45,X0_43,X1_43) = k2_xboole_0(X0_43,X1_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_1038,plain,
    ( k4_subset_1(X0_45,X0_43,k3_subset_1(X0_45,X1_43)) = k2_xboole_0(X0_43,k3_subset_1(X0_45,X1_43))
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(superposition,[status(thm)],[c_441,c_443])).

cnf(c_7090,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_43,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(X0_43,k3_subset_1(u1_struct_0(sK0),sK1))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_1038])).

cnf(c_7775,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_3300,c_7090])).

cnf(c_3308,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_43,k2_tops_1(sK0,sK1)) = k2_xboole_0(X0_43,k2_tops_1(sK0,sK1))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_443])).

cnf(c_5769,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_43),k2_tops_1(sK0,sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),X0_43),k2_tops_1(sK0,sK1))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_441,c_3308])).

cnf(c_12325,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_453,c_5769])).

cnf(c_35969,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_35928,c_7775,c_12325])).

cnf(c_35982,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(demodulation,[status(thm)],[c_35969,c_12325])).

cnf(c_37881,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37821,c_1390,c_35982])).

cnf(c_38735,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37881,c_15])).

cnf(c_38741,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(demodulation,[status(thm)],[c_38735,c_7775])).

cnf(c_4,plain,
    ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_155,plain,
    ( r1_tarski(k3_subset_1(X0_45,k4_subset_1(X0_45,X0_43,X1_43)),k3_subset_1(X0_45,X0_43))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_444,plain,
    ( r1_tarski(k3_subset_1(X0_45,k4_subset_1(X0_45,X0_43,X1_43)),k3_subset_1(X0_45,X0_43)) = iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_39727,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_38741,c_444])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_152,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k1_tops_1(X0_42,X0_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_447,plain,
    ( k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k1_tops_1(X0_42,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_2451,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_447])).

cnf(c_203,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_2858,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2451,c_14,c_13,c_203])).

cnf(c_39728,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_39727,c_2858])).

cnf(c_578,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_579,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_40117,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39728,c_15,c_16,c_210,c_579])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_157,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_442,plain,
    ( k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_3312,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3300,c_442])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k3_subset_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_154,plain,
    ( r1_xboole_0(X0_43,k3_subset_1(X0_45,X1_43))
    | ~ r1_tarski(X0_43,X1_43)
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_445,plain,
    ( r1_xboole_0(X0_43,k3_subset_1(X0_45,X1_43)) = iProver_top
    | r1_tarski(X0_43,X1_43) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_4031,plain,
    ( r1_xboole_0(X0_43,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0_43,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3312,c_445])).

cnf(c_581,plain,
    ( ~ m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k3_subset_1(u1_struct_0(X0_42),k2_tops_1(X0_42,X0_43)),k1_zfmisc_1(u1_struct_0(X0_42))) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_582,plain,
    ( m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(X0_42),k2_tops_1(X0_42,X0_43)),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_584,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_65015,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_43,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) != iProver_top
    | r1_xboole_0(X0_43,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4031,c_15,c_16,c_210,c_584])).

cnf(c_65016,plain,
    ( r1_xboole_0(X0_43,k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0_43,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_65015])).

cnf(c_65027,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_40117,c_65016])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_151,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_205,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_207,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_12,negated_conjecture,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65027,c_207,c_17,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 19.89/3.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.89/3.05  
% 19.89/3.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.89/3.05  
% 19.89/3.05  ------  iProver source info
% 19.89/3.05  
% 19.89/3.05  git: date: 2020-06-30 10:37:57 +0100
% 19.89/3.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.89/3.05  git: non_committed_changes: false
% 19.89/3.05  git: last_make_outside_of_git: false
% 19.89/3.05  
% 19.89/3.05  ------ 
% 19.89/3.05  ------ Parsing...
% 19.89/3.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.89/3.05  
% 19.89/3.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.89/3.05  
% 19.89/3.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.89/3.05  
% 19.89/3.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.89/3.05  ------ Proving...
% 19.89/3.05  ------ Problem Properties 
% 19.89/3.05  
% 19.89/3.05  
% 19.89/3.05  clauses                                 15
% 19.89/3.05  conjectures                             3
% 19.89/3.05  EPR                                     1
% 19.89/3.05  Horn                                    15
% 19.89/3.05  unary                                   3
% 19.89/3.05  binary                                  2
% 19.89/3.05  lits                                    39
% 19.89/3.05  lits eq                                 6
% 19.89/3.05  fd_pure                                 0
% 19.89/3.05  fd_pseudo                               0
% 19.89/3.05  fd_cond                                 0
% 19.89/3.05  fd_pseudo_cond                          0
% 19.89/3.05  AC symbols                              0
% 19.89/3.05  
% 19.89/3.05  ------ Input Options Time Limit: Unbounded
% 19.89/3.05  
% 19.89/3.05  
% 19.89/3.05  ------ 
% 19.89/3.05  Current options:
% 19.89/3.05  ------ 
% 19.89/3.05  
% 19.89/3.05  
% 19.89/3.05  
% 19.89/3.05  
% 19.89/3.05  ------ Proving...
% 19.89/3.05  
% 19.89/3.05  
% 19.89/3.05  % SZS status Theorem for theBenchmark.p
% 19.89/3.05  
% 19.89/3.05  % SZS output start CNFRefutation for theBenchmark.p
% 19.89/3.05  
% 19.89/3.05  fof(f12,conjecture,(
% 19.89/3.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f13,negated_conjecture,(
% 19.89/3.05    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 19.89/3.05    inference(negated_conjecture,[],[f12])).
% 19.89/3.05  
% 19.89/3.05  fof(f29,plain,(
% 19.89/3.05    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 19.89/3.05    inference(ennf_transformation,[],[f13])).
% 19.89/3.05  
% 19.89/3.05  fof(f32,plain,(
% 19.89/3.05    ( ! [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_xboole_0(k1_tops_1(X0,sK1),k2_tops_1(X0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.89/3.05    introduced(choice_axiom,[])).
% 19.89/3.05  
% 19.89/3.05  fof(f31,plain,(
% 19.89/3.05    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 19.89/3.05    introduced(choice_axiom,[])).
% 19.89/3.05  
% 19.89/3.05  fof(f33,plain,(
% 19.89/3.05    (~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 19.89/3.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f32,f31])).
% 19.89/3.05  
% 19.89/3.05  fof(f47,plain,(
% 19.89/3.05    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.89/3.05    inference(cnf_transformation,[],[f33])).
% 19.89/3.05  
% 19.89/3.05  fof(f2,axiom,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f16,plain,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.89/3.05    inference(ennf_transformation,[],[f2])).
% 19.89/3.05  
% 19.89/3.05  fof(f35,plain,(
% 19.89/3.05    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.89/3.05    inference(cnf_transformation,[],[f16])).
% 19.89/3.05  
% 19.89/3.05  fof(f11,axiom,(
% 19.89/3.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f28,plain,(
% 19.89/3.05    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.89/3.05    inference(ennf_transformation,[],[f11])).
% 19.89/3.05  
% 19.89/3.05  fof(f45,plain,(
% 19.89/3.05    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.89/3.05    inference(cnf_transformation,[],[f28])).
% 19.89/3.05  
% 19.89/3.05  fof(f10,axiom,(
% 19.89/3.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f27,plain,(
% 19.89/3.05    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.89/3.05    inference(ennf_transformation,[],[f10])).
% 19.89/3.05  
% 19.89/3.05  fof(f44,plain,(
% 19.89/3.05    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.89/3.05    inference(cnf_transformation,[],[f27])).
% 19.89/3.05  
% 19.89/3.05  fof(f46,plain,(
% 19.89/3.05    l1_pre_topc(sK0)),
% 19.89/3.05    inference(cnf_transformation,[],[f33])).
% 19.89/3.05  
% 19.89/3.05  fof(f9,axiom,(
% 19.89/3.05    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f25,plain,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.89/3.05    inference(ennf_transformation,[],[f9])).
% 19.89/3.05  
% 19.89/3.05  fof(f26,plain,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.89/3.05    inference(flattening,[],[f25])).
% 19.89/3.05  
% 19.89/3.05  fof(f43,plain,(
% 19.89/3.05    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.89/3.05    inference(cnf_transformation,[],[f26])).
% 19.89/3.05  
% 19.89/3.05  fof(f1,axiom,(
% 19.89/3.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f14,plain,(
% 19.89/3.05    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.89/3.05    inference(ennf_transformation,[],[f1])).
% 19.89/3.05  
% 19.89/3.05  fof(f15,plain,(
% 19.89/3.05    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.89/3.05    inference(flattening,[],[f14])).
% 19.89/3.05  
% 19.89/3.05  fof(f34,plain,(
% 19.89/3.05    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.89/3.05    inference(cnf_transformation,[],[f15])).
% 19.89/3.05  
% 19.89/3.05  fof(f4,axiom,(
% 19.89/3.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f18,plain,(
% 19.89/3.05    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.89/3.05    inference(ennf_transformation,[],[f4])).
% 19.89/3.05  
% 19.89/3.05  fof(f19,plain,(
% 19.89/3.05    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.89/3.05    inference(flattening,[],[f18])).
% 19.89/3.05  
% 19.89/3.05  fof(f37,plain,(
% 19.89/3.05    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.89/3.05    inference(cnf_transformation,[],[f19])).
% 19.89/3.05  
% 19.89/3.05  fof(f5,axiom,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f20,plain,(
% 19.89/3.05    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.89/3.05    inference(ennf_transformation,[],[f5])).
% 19.89/3.05  
% 19.89/3.05  fof(f38,plain,(
% 19.89/3.05    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.89/3.05    inference(cnf_transformation,[],[f20])).
% 19.89/3.05  
% 19.89/3.05  fof(f7,axiom,(
% 19.89/3.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f22,plain,(
% 19.89/3.05    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.89/3.05    inference(ennf_transformation,[],[f7])).
% 19.89/3.05  
% 19.89/3.05  fof(f41,plain,(
% 19.89/3.05    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.89/3.05    inference(cnf_transformation,[],[f22])).
% 19.89/3.05  
% 19.89/3.05  fof(f3,axiom,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f17,plain,(
% 19.89/3.05    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.89/3.05    inference(ennf_transformation,[],[f3])).
% 19.89/3.05  
% 19.89/3.05  fof(f36,plain,(
% 19.89/3.05    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.89/3.05    inference(cnf_transformation,[],[f17])).
% 19.89/3.05  
% 19.89/3.05  fof(f6,axiom,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f21,plain,(
% 19.89/3.05    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.89/3.05    inference(ennf_transformation,[],[f6])).
% 19.89/3.05  
% 19.89/3.05  fof(f30,plain,(
% 19.89/3.05    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.89/3.05    inference(nnf_transformation,[],[f21])).
% 19.89/3.05  
% 19.89/3.05  fof(f40,plain,(
% 19.89/3.05    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.89/3.05    inference(cnf_transformation,[],[f30])).
% 19.89/3.05  
% 19.89/3.05  fof(f8,axiom,(
% 19.89/3.05    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.89/3.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.89/3.05  
% 19.89/3.05  fof(f23,plain,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.89/3.05    inference(ennf_transformation,[],[f8])).
% 19.89/3.05  
% 19.89/3.05  fof(f24,plain,(
% 19.89/3.05    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.89/3.05    inference(flattening,[],[f23])).
% 19.89/3.05  
% 19.89/3.05  fof(f42,plain,(
% 19.89/3.05    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.89/3.05    inference(cnf_transformation,[],[f24])).
% 19.89/3.05  
% 19.89/3.05  fof(f48,plain,(
% 19.89/3.05    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 19.89/3.05    inference(cnf_transformation,[],[f33])).
% 19.89/3.05  
% 19.89/3.05  cnf(c_13,negated_conjecture,
% 19.89/3.05      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.89/3.05      inference(cnf_transformation,[],[f47]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_146,negated_conjecture,
% 19.89/3.05      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_13]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_453,plain,
% 19.89/3.05      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_146]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_1,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.89/3.05      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 19.89/3.05      inference(cnf_transformation,[],[f35]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_158,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 19.89/3.05      | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_1]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_441,plain,
% 19.89/3.05      ( m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
% 19.89/3.05      | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) = iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_11,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.89/3.05      | ~ l1_pre_topc(X1)
% 19.89/3.05      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 19.89/3.05      inference(cnf_transformation,[],[f45]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_148,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 19.89/3.05      | ~ l1_pre_topc(X0_42)
% 19.89/3.05      | k4_subset_1(u1_struct_0(X0_42),X0_43,k2_tops_1(X0_42,X0_43)) = k2_pre_topc(X0_42,X0_43) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_11]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_451,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(X0_42),X0_43,k2_tops_1(X0_42,X0_43)) = k2_pre_topc(X0_42,X0_43)
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 19.89/3.05      | l1_pre_topc(X0_42) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_2414,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(X0_42),k3_subset_1(u1_struct_0(X0_42),X0_43),k2_tops_1(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 19.89/3.05      | l1_pre_topc(X0_42) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_441,c_451]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_37821,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 19.89/3.05      | l1_pre_topc(sK0) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_453,c_2414]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_10,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.89/3.05      | ~ l1_pre_topc(X1)
% 19.89/3.05      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 19.89/3.05      inference(cnf_transformation,[],[f44]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_149,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 19.89/3.05      | ~ l1_pre_topc(X0_42)
% 19.89/3.05      | k2_tops_1(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43)) = k2_tops_1(X0_42,X0_43) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_10]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_450,plain,
% 19.89/3.05      ( k2_tops_1(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43)) = k2_tops_1(X0_42,X0_43)
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 19.89/3.05      | l1_pre_topc(X0_42) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_149]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_1353,plain,
% 19.89/3.05      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
% 19.89/3.05      | l1_pre_topc(sK0) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_453,c_450]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_14,negated_conjecture,
% 19.89/3.05      ( l1_pre_topc(sK0) ),
% 19.89/3.05      inference(cnf_transformation,[],[f46]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_212,plain,
% 19.89/3.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.89/3.05      | ~ l1_pre_topc(sK0)
% 19.89/3.05      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 19.89/3.05      inference(instantiation,[status(thm)],[c_149]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_1390,plain,
% 19.89/3.05      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 19.89/3.05      inference(global_propositional_subsumption,
% 19.89/3.05                [status(thm)],
% 19.89/3.05                [c_1353,c_14,c_13,c_212]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_9,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.89/3.05      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.89/3.05      | ~ l1_pre_topc(X1) ),
% 19.89/3.05      inference(cnf_transformation,[],[f43]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_150,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 19.89/3.05      | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
% 19.89/3.05      | ~ l1_pre_topc(X0_42) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_9]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_449,plain,
% 19.89/3.05      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 19.89/3.05      | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
% 19.89/3.05      | l1_pre_topc(X0_42) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_1393,plain,
% 19.89/3.05      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.89/3.05      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.89/3.05      | l1_pre_topc(sK0) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_1390,c_449]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_15,plain,
% 19.89/3.05      ( l1_pre_topc(sK0) = iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_16,plain,
% 19.89/3.05      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_208,plain,
% 19.89/3.05      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 19.89/3.05      | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
% 19.89/3.05      | l1_pre_topc(X0_42) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_210,plain,
% 19.89/3.05      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.89/3.05      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.89/3.05      | l1_pre_topc(sK0) != iProver_top ),
% 19.89/3.05      inference(instantiation,[status(thm)],[c_208]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_3300,plain,
% 19.89/3.05      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.89/3.05      inference(global_propositional_subsumption,
% 19.89/3.05                [status(thm)],
% 19.89/3.05                [c_1393,c_15,c_16,c_210]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_0,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.89/3.05      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.89/3.05      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 19.89/3.05      inference(cnf_transformation,[],[f34]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_159,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 19.89/3.05      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
% 19.89/3.05      | k4_subset_1(X0_45,X0_43,X1_43) = k4_subset_1(X0_45,X1_43,X0_43) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_0]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_440,plain,
% 19.89/3.05      ( k4_subset_1(X0_45,X0_43,X1_43) = k4_subset_1(X0_45,X1_43,X0_43)
% 19.89/3.05      | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_1016,plain,
% 19.89/3.05      ( k4_subset_1(X0_45,k3_subset_1(X0_45,X0_43),X1_43) = k4_subset_1(X0_45,X1_43,k3_subset_1(X0_45,X0_43))
% 19.89/3.05      | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_441,c_440]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_5210,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),X0_43)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_43),k2_tops_1(sK0,sK1))
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_3300,c_1016]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_35928,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_453,c_5210]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_3,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.89/3.05      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.89/3.05      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 19.89/3.05      inference(cnf_transformation,[],[f37]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_156,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 19.89/3.05      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
% 19.89/3.05      | k4_subset_1(X0_45,X1_43,X0_43) = k2_xboole_0(X1_43,X0_43) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_3]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_443,plain,
% 19.89/3.05      ( k4_subset_1(X0_45,X0_43,X1_43) = k2_xboole_0(X0_43,X1_43)
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
% 19.89/3.05      | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_1038,plain,
% 19.89/3.05      ( k4_subset_1(X0_45,X0_43,k3_subset_1(X0_45,X1_43)) = k2_xboole_0(X0_43,k3_subset_1(X0_45,X1_43))
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
% 19.89/3.05      | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_441,c_443]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_7090,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),X0_43,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(X0_43,k3_subset_1(u1_struct_0(sK0),sK1))
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_453,c_1038]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_7775,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_3300,c_7090]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_3308,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),X0_43,k2_tops_1(sK0,sK1)) = k2_xboole_0(X0_43,k2_tops_1(sK0,sK1))
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_3300,c_443]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_5769,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_43),k2_tops_1(sK0,sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),X0_43),k2_tops_1(sK0,sK1))
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_441,c_3308]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_12325,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_453,c_5769]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_35969,plain,
% 19.89/3.05      ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
% 19.89/3.05      inference(light_normalisation,
% 19.89/3.05                [status(thm)],
% 19.89/3.05                [c_35928,c_7775,c_12325]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_35982,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 19.89/3.05      inference(demodulation,[status(thm)],[c_35969,c_12325]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_37881,plain,
% 19.89/3.05      ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 19.89/3.05      | l1_pre_topc(sK0) != iProver_top ),
% 19.89/3.05      inference(light_normalisation,
% 19.89/3.05                [status(thm)],
% 19.89/3.05                [c_37821,c_1390,c_35982]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_38735,plain,
% 19.89/3.05      ( k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 19.89/3.05      inference(global_propositional_subsumption,
% 19.89/3.05                [status(thm)],
% 19.89/3.05                [c_37881,c_15]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_38741,plain,
% 19.89/3.05      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 19.89/3.05      inference(demodulation,[status(thm)],[c_38735,c_7775]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_4,plain,
% 19.89/3.05      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
% 19.89/3.05      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 19.89/3.05      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 19.89/3.05      inference(cnf_transformation,[],[f38]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_155,plain,
% 19.89/3.05      ( r1_tarski(k3_subset_1(X0_45,k4_subset_1(X0_45,X0_43,X1_43)),k3_subset_1(X0_45,X0_43))
% 19.89/3.05      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
% 19.89/3.05      | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_4]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_444,plain,
% 19.89/3.05      ( r1_tarski(k3_subset_1(X0_45,k4_subset_1(X0_45,X0_43,X1_43)),k3_subset_1(X0_45,X0_43)) = iProver_top
% 19.89/3.05      | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_39727,plain,
% 19.89/3.05      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
% 19.89/3.05      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.89/3.05      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_38741,c_444]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_7,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.89/3.05      | ~ l1_pre_topc(X1)
% 19.89/3.05      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 19.89/3.05      inference(cnf_transformation,[],[f41]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_152,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 19.89/3.05      | ~ l1_pre_topc(X0_42)
% 19.89/3.05      | k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k1_tops_1(X0_42,X0_43) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_7]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_447,plain,
% 19.89/3.05      ( k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_43))) = k1_tops_1(X0_42,X0_43)
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 19.89/3.05      | l1_pre_topc(X0_42) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_152]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_2451,plain,
% 19.89/3.05      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1)
% 19.89/3.05      | l1_pre_topc(sK0) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_453,c_447]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_203,plain,
% 19.89/3.05      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.89/3.05      | ~ l1_pre_topc(sK0)
% 19.89/3.05      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 19.89/3.05      inference(instantiation,[status(thm)],[c_152]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_2858,plain,
% 19.89/3.05      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 19.89/3.05      inference(global_propositional_subsumption,
% 19.89/3.05                [status(thm)],
% 19.89/3.05                [c_2451,c_14,c_13,c_203]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_39728,plain,
% 19.89/3.05      ( r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top
% 19.89/3.05      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.89/3.05      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(light_normalisation,[status(thm)],[c_39727,c_2858]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_578,plain,
% 19.89/3.05      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.89/3.05      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.89/3.05      inference(instantiation,[status(thm)],[c_158]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_579,plain,
% 19.89/3.05      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.89/3.05      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_40117,plain,
% 19.89/3.05      ( r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
% 19.89/3.05      inference(global_propositional_subsumption,
% 19.89/3.05                [status(thm)],
% 19.89/3.05                [c_39728,c_15,c_16,c_210,c_579]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_2,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.89/3.05      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 19.89/3.05      inference(cnf_transformation,[],[f36]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_157,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 19.89/3.05      | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43 ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_2]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_442,plain,
% 19.89/3.05      ( k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_3312,plain,
% 19.89/3.05      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_3300,c_442]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_5,plain,
% 19.89/3.05      ( r1_xboole_0(X0,k3_subset_1(X1,X2))
% 19.89/3.05      | ~ r1_tarski(X0,X2)
% 19.89/3.05      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.89/3.05      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.89/3.05      inference(cnf_transformation,[],[f40]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_154,plain,
% 19.89/3.05      ( r1_xboole_0(X0_43,k3_subset_1(X0_45,X1_43))
% 19.89/3.05      | ~ r1_tarski(X0_43,X1_43)
% 19.89/3.05      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
% 19.89/3.05      | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_5]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_445,plain,
% 19.89/3.05      ( r1_xboole_0(X0_43,k3_subset_1(X0_45,X1_43)) = iProver_top
% 19.89/3.05      | r1_tarski(X0_43,X1_43) != iProver_top
% 19.89/3.05      | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_4031,plain,
% 19.89/3.05      ( r1_xboole_0(X0_43,k2_tops_1(sK0,sK1)) = iProver_top
% 19.89/3.05      | r1_tarski(X0_43,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) != iProver_top
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.89/3.05      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_3312,c_445]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_581,plain,
% 19.89/3.05      ( ~ m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
% 19.89/3.05      | m1_subset_1(k3_subset_1(u1_struct_0(X0_42),k2_tops_1(X0_42,X0_43)),k1_zfmisc_1(u1_struct_0(X0_42))) ),
% 19.89/3.05      inference(instantiation,[status(thm)],[c_158]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_582,plain,
% 19.89/3.05      ( m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 19.89/3.05      | m1_subset_1(k3_subset_1(u1_struct_0(X0_42),k2_tops_1(X0_42,X0_43)),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_584,plain,
% 19.89/3.05      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.89/3.05      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.89/3.05      inference(instantiation,[status(thm)],[c_582]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_65015,plain,
% 19.89/3.05      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.89/3.05      | r1_tarski(X0_43,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) != iProver_top
% 19.89/3.05      | r1_xboole_0(X0_43,k2_tops_1(sK0,sK1)) = iProver_top ),
% 19.89/3.05      inference(global_propositional_subsumption,
% 19.89/3.05                [status(thm)],
% 19.89/3.05                [c_4031,c_15,c_16,c_210,c_584]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_65016,plain,
% 19.89/3.05      ( r1_xboole_0(X0_43,k2_tops_1(sK0,sK1)) = iProver_top
% 19.89/3.05      | r1_tarski(X0_43,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) != iProver_top
% 19.89/3.05      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(renaming,[status(thm)],[c_65015]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_65027,plain,
% 19.89/3.05      ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = iProver_top
% 19.89/3.05      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.89/3.05      inference(superposition,[status(thm)],[c_40117,c_65016]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_8,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.89/3.05      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.89/3.05      | ~ l1_pre_topc(X1) ),
% 19.89/3.05      inference(cnf_transformation,[],[f42]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_151,plain,
% 19.89/3.05      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 19.89/3.05      | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
% 19.89/3.05      | ~ l1_pre_topc(X0_42) ),
% 19.89/3.05      inference(subtyping,[status(esa)],[c_8]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_205,plain,
% 19.89/3.05      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 19.89/3.05      | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
% 19.89/3.05      | l1_pre_topc(X0_42) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_207,plain,
% 19.89/3.05      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.89/3.05      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.89/3.05      | l1_pre_topc(sK0) != iProver_top ),
% 19.89/3.05      inference(instantiation,[status(thm)],[c_205]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_12,negated_conjecture,
% 19.89/3.05      ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
% 19.89/3.05      inference(cnf_transformation,[],[f48]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(c_17,plain,
% 19.89/3.05      ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) != iProver_top ),
% 19.89/3.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.89/3.05  
% 19.89/3.05  cnf(contradiction,plain,
% 19.89/3.05      ( $false ),
% 19.89/3.05      inference(minisat,[status(thm)],[c_65027,c_207,c_17,c_16,c_15]) ).
% 19.89/3.05  
% 19.89/3.05  
% 19.89/3.05  % SZS output end CNFRefutation for theBenchmark.p
% 19.89/3.05  
% 19.89/3.05  ------                               Statistics
% 19.89/3.05  
% 19.89/3.05  ------ Selected
% 19.89/3.05  
% 19.89/3.05  total_time:                             2.225
% 19.89/3.05  
%------------------------------------------------------------------------------
