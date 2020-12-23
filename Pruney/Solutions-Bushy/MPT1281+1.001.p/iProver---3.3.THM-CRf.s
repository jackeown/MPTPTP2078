%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1281+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:19 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 214 expanded)
%              Number of clauses        :   52 (  71 expanded)
%              Number of leaves         :   11 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  214 ( 712 expanded)
%              Number of equality atoms :   66 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
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

fof(f26,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25,f24])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_294,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_455,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_192,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_458,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_168,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
    inference(subtyping,[status(esa)],[c_169])).

cnf(c_456,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_628,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_458,c_456])).

cnf(c_1041,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_455,c_628])).

cnf(c_2,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_160,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_162,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_160,c_12,c_11])).

cnf(c_292,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_162])).

cnf(c_1058,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1041,c_292])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_42),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_42))) = k2_tops_1(sK0,X0_42) ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_459,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_42),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_42))) = k2_tops_1(sK0,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_635,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_455,c_459])).

cnf(c_1163,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1058,c_635])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
    | m1_subset_1(k3_subset_1(X0_44,X0_42),k1_zfmisc_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_453,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_44,X0_42),k1_zfmisc_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_181])).

cnf(c_457,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
    | k9_subset_1(X0_44,X1_42,X0_42) = k3_xboole_0(X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_454,plain,
    ( k9_subset_1(X0_44,X0_42,X1_42) = k3_xboole_0(X0_42,X1_42)
    | m1_subset_1(X1_42,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_724,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_42,k2_pre_topc(sK0,X1_42)) = k3_xboole_0(X0_42,k2_pre_topc(sK0,X1_42))
    | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_457,c_454])).

cnf(c_1433,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_42,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1_42))) = k3_xboole_0(X0_42,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1_42)))
    | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_724])).

cnf(c_3588,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_42,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_xboole_0(X0_42,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(superposition,[status(thm)],[c_455,c_1433])).

cnf(c_3617,plain,
    ( k3_xboole_0(sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1163,c_3588])).

cnf(c_8,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_151,plain,
    ( k3_xboole_0(X0,X1) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_152,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != k2_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_293,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0_42) != k2_tops_1(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_152])).

cnf(c_464,plain,
    ( k3_xboole_0(sK1,X0_42) != k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_293,c_292])).

cnf(c_3958,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3617,c_464])).


%------------------------------------------------------------------------------
