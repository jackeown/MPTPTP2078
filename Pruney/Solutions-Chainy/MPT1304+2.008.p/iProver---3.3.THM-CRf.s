%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:27 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 254 expanded)
%              Number of clauses        :   54 ( 101 expanded)
%              Number of leaves         :   14 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  218 ( 742 expanded)
%              Number of equality atoms :   74 ( 137 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v1_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              | ~ v1_tops_2(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              | ~ v1_tops_2(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k4_xboole_0(X2,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_156,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_155])).

cnf(c_273,plain,
    ( m1_subset_1(k4_xboole_0(X0_43,X1_43),k1_zfmisc_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_156])).

cnf(c_521,plain,
    ( m1_subset_1(k4_xboole_0(X0_43,X1_43),k1_zfmisc_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | k3_subset_1(X1_43,k3_subset_1(X1_43,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_514,plain,
    ( k3_subset_1(X0_43,k3_subset_1(X0_43,X1_43)) = X1_43
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_1034,plain,
    ( k3_subset_1(X0_43,k3_subset_1(X0_43,k4_xboole_0(X0_43,X1_43))) = k4_xboole_0(X0_43,X1_43) ),
    inference(superposition,[status(thm)],[c_521,c_514])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | k3_subset_1(X1_43,X0_43) = k4_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_512,plain,
    ( k3_subset_1(X0_43,X1_43) = k4_xboole_0(X0_43,X1_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_895,plain,
    ( k3_subset_1(X0_43,k4_xboole_0(X0_43,X1_43)) = k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) ),
    inference(superposition,[status(thm)],[c_521,c_512])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_278,plain,
    ( k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) = k1_setfam_1(k2_tarski(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_900,plain,
    ( k3_subset_1(X0_43,k4_xboole_0(X0_43,X1_43)) = k1_setfam_1(k2_tarski(X0_43,X1_43)) ),
    inference(light_normalisation,[status(thm)],[c_895,c_278])).

cnf(c_909,plain,
    ( k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(X0_43,X1_43))) = k3_subset_1(X0_43,k1_setfam_1(k2_tarski(X0_43,X1_43))) ),
    inference(superposition,[status(thm)],[c_278,c_900])).

cnf(c_1040,plain,
    ( k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(X0_43,X1_43))) = k4_xboole_0(X0_43,X1_43) ),
    inference(light_normalisation,[status(thm)],[c_1034,c_900,c_909])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_274,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_520,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | k7_subset_1(X1_43,X0_43,X2_43) = k4_xboole_0(X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_515,plain,
    ( k7_subset_1(X0_43,X1_43,X2_43) = k4_xboole_0(X1_43,X2_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_1753,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_43) = k4_xboole_0(sK1,X0_43) ),
    inference(superposition,[status(thm)],[c_520,c_515])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | m1_subset_1(k7_subset_1(X1_43,X0_43,X2_43),k1_zfmisc_1(X1_43)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_513,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | m1_subset_1(k7_subset_1(X1_43,X0_43,X2_43),k1_zfmisc_1(X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_2065,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_513])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2356,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2065,c_15])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | k4_xboole_0(X2_43,k4_xboole_0(X2_43,X0_43)) = k9_subset_1(X1_43,X2_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_516,plain,
    ( k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) = k9_subset_1(X2_43,X0_43,X1_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(X2_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_551,plain,
    ( k9_subset_1(X0_43,X1_43,X2_43) = k1_setfam_1(k2_tarski(X1_43,X2_43))
    | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_516,c_278])).

cnf(c_2370,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_43,k4_xboole_0(sK1,X1_43)) = k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(sK1,X1_43))) ),
    inference(superposition,[status(thm)],[c_2356,c_551])).

cnf(c_8,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X0,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_166,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X0,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_167,plain,
    ( ~ v1_tops_2(X0,sK0)
    | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,X1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_272,plain,
    ( ~ v1_tops_2(X0_43,sK0)
    | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_43,X1_43),sK0)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_167])).

cnf(c_522,plain,
    ( v1_tops_2(X0_43,sK0) != iProver_top
    | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_43,X1_43),sK0) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_4081,plain,
    ( v1_tops_2(X0_43,sK0) != iProver_top
    | v1_tops_2(k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(sK1,X1_43))),sK0) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k4_xboole_0(sK1,X1_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2370,c_522])).

cnf(c_4103,plain,
    ( v1_tops_2(X0_43,sK0) != iProver_top
    | v1_tops_2(k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(sK1,X1_43))),sK0) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4081,c_2356])).

cnf(c_4107,plain,
    ( v1_tops_2(k4_xboole_0(sK1,X0_43),sK0) = iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_4103])).

cnf(c_10,negated_conjecture,
    ( v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( v1_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12508,plain,
    ( v1_tops_2(k4_xboole_0(sK1,X0_43),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4107,c_15,c_17])).

cnf(c_9,negated_conjecture,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_277,negated_conjecture,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_517,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_2063,plain,
    ( v1_tops_2(k4_xboole_0(sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1753,c_517])).

cnf(c_12517,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_12508,c_2063])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.81/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/1.02  
% 3.81/1.02  ------  iProver source info
% 3.81/1.02  
% 3.81/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.81/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/1.02  git: non_committed_changes: false
% 3.81/1.02  git: last_make_outside_of_git: false
% 3.81/1.02  
% 3.81/1.02  ------ 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options
% 3.81/1.02  
% 3.81/1.02  --out_options                           all
% 3.81/1.02  --tptp_safe_out                         true
% 3.81/1.02  --problem_path                          ""
% 3.81/1.02  --include_path                          ""
% 3.81/1.02  --clausifier                            res/vclausify_rel
% 3.81/1.02  --clausifier_options                    --mode clausify
% 3.81/1.02  --stdin                                 false
% 3.81/1.02  --stats_out                             all
% 3.81/1.02  
% 3.81/1.02  ------ General Options
% 3.81/1.02  
% 3.81/1.02  --fof                                   false
% 3.81/1.02  --time_out_real                         305.
% 3.81/1.02  --time_out_virtual                      -1.
% 3.81/1.02  --symbol_type_check                     false
% 3.81/1.02  --clausify_out                          false
% 3.81/1.02  --sig_cnt_out                           false
% 3.81/1.02  --trig_cnt_out                          false
% 3.81/1.02  --trig_cnt_out_tolerance                1.
% 3.81/1.02  --trig_cnt_out_sk_spl                   false
% 3.81/1.02  --abstr_cl_out                          false
% 3.81/1.02  
% 3.81/1.02  ------ Global Options
% 3.81/1.02  
% 3.81/1.02  --schedule                              default
% 3.81/1.02  --add_important_lit                     false
% 3.81/1.02  --prop_solver_per_cl                    1000
% 3.81/1.02  --min_unsat_core                        false
% 3.81/1.02  --soft_assumptions                      false
% 3.81/1.02  --soft_lemma_size                       3
% 3.81/1.02  --prop_impl_unit_size                   0
% 3.81/1.02  --prop_impl_unit                        []
% 3.81/1.02  --share_sel_clauses                     true
% 3.81/1.02  --reset_solvers                         false
% 3.81/1.02  --bc_imp_inh                            [conj_cone]
% 3.81/1.02  --conj_cone_tolerance                   3.
% 3.81/1.02  --extra_neg_conj                        none
% 3.81/1.02  --large_theory_mode                     true
% 3.81/1.02  --prolific_symb_bound                   200
% 3.81/1.02  --lt_threshold                          2000
% 3.81/1.02  --clause_weak_htbl                      true
% 3.81/1.02  --gc_record_bc_elim                     false
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing Options
% 3.81/1.02  
% 3.81/1.02  --preprocessing_flag                    true
% 3.81/1.02  --time_out_prep_mult                    0.1
% 3.81/1.02  --splitting_mode                        input
% 3.81/1.02  --splitting_grd                         true
% 3.81/1.02  --splitting_cvd                         false
% 3.81/1.02  --splitting_cvd_svl                     false
% 3.81/1.02  --splitting_nvd                         32
% 3.81/1.02  --sub_typing                            true
% 3.81/1.02  --prep_gs_sim                           true
% 3.81/1.02  --prep_unflatten                        true
% 3.81/1.02  --prep_res_sim                          true
% 3.81/1.02  --prep_upred                            true
% 3.81/1.02  --prep_sem_filter                       exhaustive
% 3.81/1.02  --prep_sem_filter_out                   false
% 3.81/1.02  --pred_elim                             true
% 3.81/1.02  --res_sim_input                         true
% 3.81/1.02  --eq_ax_congr_red                       true
% 3.81/1.02  --pure_diseq_elim                       true
% 3.81/1.02  --brand_transform                       false
% 3.81/1.02  --non_eq_to_eq                          false
% 3.81/1.02  --prep_def_merge                        true
% 3.81/1.02  --prep_def_merge_prop_impl              false
% 3.81/1.02  --prep_def_merge_mbd                    true
% 3.81/1.02  --prep_def_merge_tr_red                 false
% 3.81/1.02  --prep_def_merge_tr_cl                  false
% 3.81/1.02  --smt_preprocessing                     true
% 3.81/1.02  --smt_ac_axioms                         fast
% 3.81/1.02  --preprocessed_out                      false
% 3.81/1.02  --preprocessed_stats                    false
% 3.81/1.02  
% 3.81/1.02  ------ Abstraction refinement Options
% 3.81/1.02  
% 3.81/1.02  --abstr_ref                             []
% 3.81/1.02  --abstr_ref_prep                        false
% 3.81/1.02  --abstr_ref_until_sat                   false
% 3.81/1.02  --abstr_ref_sig_restrict                funpre
% 3.81/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.02  --abstr_ref_under                       []
% 3.81/1.02  
% 3.81/1.02  ------ SAT Options
% 3.81/1.02  
% 3.81/1.02  --sat_mode                              false
% 3.81/1.02  --sat_fm_restart_options                ""
% 3.81/1.02  --sat_gr_def                            false
% 3.81/1.02  --sat_epr_types                         true
% 3.81/1.02  --sat_non_cyclic_types                  false
% 3.81/1.02  --sat_finite_models                     false
% 3.81/1.02  --sat_fm_lemmas                         false
% 3.81/1.02  --sat_fm_prep                           false
% 3.81/1.02  --sat_fm_uc_incr                        true
% 3.81/1.02  --sat_out_model                         small
% 3.81/1.02  --sat_out_clauses                       false
% 3.81/1.02  
% 3.81/1.02  ------ QBF Options
% 3.81/1.02  
% 3.81/1.02  --qbf_mode                              false
% 3.81/1.02  --qbf_elim_univ                         false
% 3.81/1.02  --qbf_dom_inst                          none
% 3.81/1.02  --qbf_dom_pre_inst                      false
% 3.81/1.02  --qbf_sk_in                             false
% 3.81/1.02  --qbf_pred_elim                         true
% 3.81/1.02  --qbf_split                             512
% 3.81/1.02  
% 3.81/1.02  ------ BMC1 Options
% 3.81/1.02  
% 3.81/1.02  --bmc1_incremental                      false
% 3.81/1.02  --bmc1_axioms                           reachable_all
% 3.81/1.02  --bmc1_min_bound                        0
% 3.81/1.02  --bmc1_max_bound                        -1
% 3.81/1.02  --bmc1_max_bound_default                -1
% 3.81/1.02  --bmc1_symbol_reachability              true
% 3.81/1.02  --bmc1_property_lemmas                  false
% 3.81/1.02  --bmc1_k_induction                      false
% 3.81/1.02  --bmc1_non_equiv_states                 false
% 3.81/1.02  --bmc1_deadlock                         false
% 3.81/1.02  --bmc1_ucm                              false
% 3.81/1.02  --bmc1_add_unsat_core                   none
% 3.81/1.02  --bmc1_unsat_core_children              false
% 3.81/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.02  --bmc1_out_stat                         full
% 3.81/1.02  --bmc1_ground_init                      false
% 3.81/1.02  --bmc1_pre_inst_next_state              false
% 3.81/1.02  --bmc1_pre_inst_state                   false
% 3.81/1.02  --bmc1_pre_inst_reach_state             false
% 3.81/1.02  --bmc1_out_unsat_core                   false
% 3.81/1.02  --bmc1_aig_witness_out                  false
% 3.81/1.02  --bmc1_verbose                          false
% 3.81/1.02  --bmc1_dump_clauses_tptp                false
% 3.81/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.02  --bmc1_dump_file                        -
% 3.81/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.02  --bmc1_ucm_extend_mode                  1
% 3.81/1.02  --bmc1_ucm_init_mode                    2
% 3.81/1.02  --bmc1_ucm_cone_mode                    none
% 3.81/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.02  --bmc1_ucm_relax_model                  4
% 3.81/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.02  --bmc1_ucm_layered_model                none
% 3.81/1.02  --bmc1_ucm_max_lemma_size               10
% 3.81/1.02  
% 3.81/1.02  ------ AIG Options
% 3.81/1.02  
% 3.81/1.02  --aig_mode                              false
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation Options
% 3.81/1.02  
% 3.81/1.02  --instantiation_flag                    true
% 3.81/1.02  --inst_sos_flag                         false
% 3.81/1.02  --inst_sos_phase                        true
% 3.81/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel_side                     num_symb
% 3.81/1.02  --inst_solver_per_active                1400
% 3.81/1.02  --inst_solver_calls_frac                1.
% 3.81/1.02  --inst_passive_queue_type               priority_queues
% 3.81/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.02  --inst_passive_queues_freq              [25;2]
% 3.81/1.02  --inst_dismatching                      true
% 3.81/1.02  --inst_eager_unprocessed_to_passive     true
% 3.81/1.02  --inst_prop_sim_given                   true
% 3.81/1.02  --inst_prop_sim_new                     false
% 3.81/1.02  --inst_subs_new                         false
% 3.81/1.02  --inst_eq_res_simp                      false
% 3.81/1.02  --inst_subs_given                       false
% 3.81/1.02  --inst_orphan_elimination               true
% 3.81/1.02  --inst_learning_loop_flag               true
% 3.81/1.02  --inst_learning_start                   3000
% 3.81/1.02  --inst_learning_factor                  2
% 3.81/1.02  --inst_start_prop_sim_after_learn       3
% 3.81/1.02  --inst_sel_renew                        solver
% 3.81/1.02  --inst_lit_activity_flag                true
% 3.81/1.02  --inst_restr_to_given                   false
% 3.81/1.02  --inst_activity_threshold               500
% 3.81/1.02  --inst_out_proof                        true
% 3.81/1.02  
% 3.81/1.02  ------ Resolution Options
% 3.81/1.02  
% 3.81/1.02  --resolution_flag                       true
% 3.81/1.02  --res_lit_sel                           adaptive
% 3.81/1.02  --res_lit_sel_side                      none
% 3.81/1.02  --res_ordering                          kbo
% 3.81/1.02  --res_to_prop_solver                    active
% 3.81/1.02  --res_prop_simpl_new                    false
% 3.81/1.02  --res_prop_simpl_given                  true
% 3.81/1.02  --res_passive_queue_type                priority_queues
% 3.81/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.02  --res_passive_queues_freq               [15;5]
% 3.81/1.02  --res_forward_subs                      full
% 3.81/1.02  --res_backward_subs                     full
% 3.81/1.02  --res_forward_subs_resolution           true
% 3.81/1.02  --res_backward_subs_resolution          true
% 3.81/1.02  --res_orphan_elimination                true
% 3.81/1.02  --res_time_limit                        2.
% 3.81/1.02  --res_out_proof                         true
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Options
% 3.81/1.02  
% 3.81/1.02  --superposition_flag                    true
% 3.81/1.02  --sup_passive_queue_type                priority_queues
% 3.81/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.02  --demod_completeness_check              fast
% 3.81/1.02  --demod_use_ground                      true
% 3.81/1.02  --sup_to_prop_solver                    passive
% 3.81/1.02  --sup_prop_simpl_new                    true
% 3.81/1.02  --sup_prop_simpl_given                  true
% 3.81/1.02  --sup_fun_splitting                     false
% 3.81/1.02  --sup_smt_interval                      50000
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Simplification Setup
% 3.81/1.02  
% 3.81/1.02  --sup_indices_passive                   []
% 3.81/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_full_bw                           [BwDemod]
% 3.81/1.02  --sup_immed_triv                        [TrivRules]
% 3.81/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_immed_bw_main                     []
% 3.81/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.02  
% 3.81/1.02  ------ Combination Options
% 3.81/1.02  
% 3.81/1.02  --comb_res_mult                         3
% 3.81/1.02  --comb_sup_mult                         2
% 3.81/1.02  --comb_inst_mult                        10
% 3.81/1.02  
% 3.81/1.02  ------ Debug Options
% 3.81/1.02  
% 3.81/1.02  --dbg_backtrace                         false
% 3.81/1.02  --dbg_dump_prop_clauses                 false
% 3.81/1.02  --dbg_dump_prop_clauses_file            -
% 3.81/1.02  --dbg_out_stat                          false
% 3.81/1.02  ------ Parsing...
% 3.81/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.02  ------ Proving...
% 3.81/1.02  ------ Problem Properties 
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  clauses                                 12
% 3.81/1.02  conjectures                             4
% 3.81/1.02  EPR                                     1
% 3.81/1.02  Horn                                    12
% 3.81/1.02  unary                                   6
% 3.81/1.02  binary                                  5
% 3.81/1.02  lits                                    20
% 3.81/1.02  lits eq                                 5
% 3.81/1.02  fd_pure                                 0
% 3.81/1.02  fd_pseudo                               0
% 3.81/1.02  fd_cond                                 0
% 3.81/1.02  fd_pseudo_cond                          0
% 3.81/1.02  AC symbols                              0
% 3.81/1.02  
% 3.81/1.02  ------ Schedule dynamic 5 is on 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  ------ 
% 3.81/1.02  Current options:
% 3.81/1.02  ------ 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options
% 3.81/1.02  
% 3.81/1.02  --out_options                           all
% 3.81/1.02  --tptp_safe_out                         true
% 3.81/1.02  --problem_path                          ""
% 3.81/1.02  --include_path                          ""
% 3.81/1.02  --clausifier                            res/vclausify_rel
% 3.81/1.02  --clausifier_options                    --mode clausify
% 3.81/1.02  --stdin                                 false
% 3.81/1.02  --stats_out                             all
% 3.81/1.02  
% 3.81/1.02  ------ General Options
% 3.81/1.02  
% 3.81/1.02  --fof                                   false
% 3.81/1.02  --time_out_real                         305.
% 3.81/1.02  --time_out_virtual                      -1.
% 3.81/1.02  --symbol_type_check                     false
% 3.81/1.02  --clausify_out                          false
% 3.81/1.02  --sig_cnt_out                           false
% 3.81/1.02  --trig_cnt_out                          false
% 3.81/1.02  --trig_cnt_out_tolerance                1.
% 3.81/1.02  --trig_cnt_out_sk_spl                   false
% 3.81/1.02  --abstr_cl_out                          false
% 3.81/1.02  
% 3.81/1.02  ------ Global Options
% 3.81/1.02  
% 3.81/1.02  --schedule                              default
% 3.81/1.02  --add_important_lit                     false
% 3.81/1.02  --prop_solver_per_cl                    1000
% 3.81/1.02  --min_unsat_core                        false
% 3.81/1.02  --soft_assumptions                      false
% 3.81/1.02  --soft_lemma_size                       3
% 3.81/1.02  --prop_impl_unit_size                   0
% 3.81/1.02  --prop_impl_unit                        []
% 3.81/1.02  --share_sel_clauses                     true
% 3.81/1.02  --reset_solvers                         false
% 3.81/1.02  --bc_imp_inh                            [conj_cone]
% 3.81/1.02  --conj_cone_tolerance                   3.
% 3.81/1.02  --extra_neg_conj                        none
% 3.81/1.02  --large_theory_mode                     true
% 3.81/1.02  --prolific_symb_bound                   200
% 3.81/1.02  --lt_threshold                          2000
% 3.81/1.02  --clause_weak_htbl                      true
% 3.81/1.02  --gc_record_bc_elim                     false
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing Options
% 3.81/1.02  
% 3.81/1.02  --preprocessing_flag                    true
% 3.81/1.02  --time_out_prep_mult                    0.1
% 3.81/1.02  --splitting_mode                        input
% 3.81/1.02  --splitting_grd                         true
% 3.81/1.02  --splitting_cvd                         false
% 3.81/1.02  --splitting_cvd_svl                     false
% 3.81/1.02  --splitting_nvd                         32
% 3.81/1.02  --sub_typing                            true
% 3.81/1.02  --prep_gs_sim                           true
% 3.81/1.02  --prep_unflatten                        true
% 3.81/1.02  --prep_res_sim                          true
% 3.81/1.02  --prep_upred                            true
% 3.81/1.02  --prep_sem_filter                       exhaustive
% 3.81/1.02  --prep_sem_filter_out                   false
% 3.81/1.02  --pred_elim                             true
% 3.81/1.02  --res_sim_input                         true
% 3.81/1.02  --eq_ax_congr_red                       true
% 3.81/1.02  --pure_diseq_elim                       true
% 3.81/1.02  --brand_transform                       false
% 3.81/1.02  --non_eq_to_eq                          false
% 3.81/1.02  --prep_def_merge                        true
% 3.81/1.02  --prep_def_merge_prop_impl              false
% 3.81/1.02  --prep_def_merge_mbd                    true
% 3.81/1.02  --prep_def_merge_tr_red                 false
% 3.81/1.02  --prep_def_merge_tr_cl                  false
% 3.81/1.02  --smt_preprocessing                     true
% 3.81/1.02  --smt_ac_axioms                         fast
% 3.81/1.02  --preprocessed_out                      false
% 3.81/1.02  --preprocessed_stats                    false
% 3.81/1.02  
% 3.81/1.02  ------ Abstraction refinement Options
% 3.81/1.02  
% 3.81/1.02  --abstr_ref                             []
% 3.81/1.02  --abstr_ref_prep                        false
% 3.81/1.02  --abstr_ref_until_sat                   false
% 3.81/1.02  --abstr_ref_sig_restrict                funpre
% 3.81/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.02  --abstr_ref_under                       []
% 3.81/1.02  
% 3.81/1.02  ------ SAT Options
% 3.81/1.02  
% 3.81/1.02  --sat_mode                              false
% 3.81/1.02  --sat_fm_restart_options                ""
% 3.81/1.02  --sat_gr_def                            false
% 3.81/1.02  --sat_epr_types                         true
% 3.81/1.02  --sat_non_cyclic_types                  false
% 3.81/1.02  --sat_finite_models                     false
% 3.81/1.02  --sat_fm_lemmas                         false
% 3.81/1.02  --sat_fm_prep                           false
% 3.81/1.02  --sat_fm_uc_incr                        true
% 3.81/1.02  --sat_out_model                         small
% 3.81/1.02  --sat_out_clauses                       false
% 3.81/1.02  
% 3.81/1.02  ------ QBF Options
% 3.81/1.02  
% 3.81/1.02  --qbf_mode                              false
% 3.81/1.02  --qbf_elim_univ                         false
% 3.81/1.02  --qbf_dom_inst                          none
% 3.81/1.02  --qbf_dom_pre_inst                      false
% 3.81/1.02  --qbf_sk_in                             false
% 3.81/1.02  --qbf_pred_elim                         true
% 3.81/1.02  --qbf_split                             512
% 3.81/1.02  
% 3.81/1.02  ------ BMC1 Options
% 3.81/1.02  
% 3.81/1.02  --bmc1_incremental                      false
% 3.81/1.02  --bmc1_axioms                           reachable_all
% 3.81/1.02  --bmc1_min_bound                        0
% 3.81/1.02  --bmc1_max_bound                        -1
% 3.81/1.02  --bmc1_max_bound_default                -1
% 3.81/1.02  --bmc1_symbol_reachability              true
% 3.81/1.02  --bmc1_property_lemmas                  false
% 3.81/1.02  --bmc1_k_induction                      false
% 3.81/1.02  --bmc1_non_equiv_states                 false
% 3.81/1.02  --bmc1_deadlock                         false
% 3.81/1.02  --bmc1_ucm                              false
% 3.81/1.02  --bmc1_add_unsat_core                   none
% 3.81/1.02  --bmc1_unsat_core_children              false
% 3.81/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.02  --bmc1_out_stat                         full
% 3.81/1.02  --bmc1_ground_init                      false
% 3.81/1.02  --bmc1_pre_inst_next_state              false
% 3.81/1.02  --bmc1_pre_inst_state                   false
% 3.81/1.02  --bmc1_pre_inst_reach_state             false
% 3.81/1.02  --bmc1_out_unsat_core                   false
% 3.81/1.02  --bmc1_aig_witness_out                  false
% 3.81/1.02  --bmc1_verbose                          false
% 3.81/1.02  --bmc1_dump_clauses_tptp                false
% 3.81/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.02  --bmc1_dump_file                        -
% 3.81/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.02  --bmc1_ucm_extend_mode                  1
% 3.81/1.02  --bmc1_ucm_init_mode                    2
% 3.81/1.02  --bmc1_ucm_cone_mode                    none
% 3.81/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.02  --bmc1_ucm_relax_model                  4
% 3.81/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.02  --bmc1_ucm_layered_model                none
% 3.81/1.02  --bmc1_ucm_max_lemma_size               10
% 3.81/1.02  
% 3.81/1.02  ------ AIG Options
% 3.81/1.02  
% 3.81/1.02  --aig_mode                              false
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation Options
% 3.81/1.02  
% 3.81/1.02  --instantiation_flag                    true
% 3.81/1.02  --inst_sos_flag                         false
% 3.81/1.02  --inst_sos_phase                        true
% 3.81/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel_side                     none
% 3.81/1.02  --inst_solver_per_active                1400
% 3.81/1.02  --inst_solver_calls_frac                1.
% 3.81/1.02  --inst_passive_queue_type               priority_queues
% 3.81/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.02  --inst_passive_queues_freq              [25;2]
% 3.81/1.02  --inst_dismatching                      true
% 3.81/1.02  --inst_eager_unprocessed_to_passive     true
% 3.81/1.02  --inst_prop_sim_given                   true
% 3.81/1.02  --inst_prop_sim_new                     false
% 3.81/1.02  --inst_subs_new                         false
% 3.81/1.02  --inst_eq_res_simp                      false
% 3.81/1.02  --inst_subs_given                       false
% 3.81/1.02  --inst_orphan_elimination               true
% 3.81/1.02  --inst_learning_loop_flag               true
% 3.81/1.02  --inst_learning_start                   3000
% 3.81/1.02  --inst_learning_factor                  2
% 3.81/1.02  --inst_start_prop_sim_after_learn       3
% 3.81/1.02  --inst_sel_renew                        solver
% 3.81/1.02  --inst_lit_activity_flag                true
% 3.81/1.02  --inst_restr_to_given                   false
% 3.81/1.02  --inst_activity_threshold               500
% 3.81/1.02  --inst_out_proof                        true
% 3.81/1.02  
% 3.81/1.02  ------ Resolution Options
% 3.81/1.02  
% 3.81/1.02  --resolution_flag                       false
% 3.81/1.02  --res_lit_sel                           adaptive
% 3.81/1.02  --res_lit_sel_side                      none
% 3.81/1.02  --res_ordering                          kbo
% 3.81/1.02  --res_to_prop_solver                    active
% 3.81/1.02  --res_prop_simpl_new                    false
% 3.81/1.02  --res_prop_simpl_given                  true
% 3.81/1.02  --res_passive_queue_type                priority_queues
% 3.81/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.02  --res_passive_queues_freq               [15;5]
% 3.81/1.02  --res_forward_subs                      full
% 3.81/1.02  --res_backward_subs                     full
% 3.81/1.02  --res_forward_subs_resolution           true
% 3.81/1.02  --res_backward_subs_resolution          true
% 3.81/1.02  --res_orphan_elimination                true
% 3.81/1.02  --res_time_limit                        2.
% 3.81/1.02  --res_out_proof                         true
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Options
% 3.81/1.02  
% 3.81/1.02  --superposition_flag                    true
% 3.81/1.02  --sup_passive_queue_type                priority_queues
% 3.81/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.02  --demod_completeness_check              fast
% 3.81/1.02  --demod_use_ground                      true
% 3.81/1.02  --sup_to_prop_solver                    passive
% 3.81/1.02  --sup_prop_simpl_new                    true
% 3.81/1.02  --sup_prop_simpl_given                  true
% 3.81/1.02  --sup_fun_splitting                     false
% 3.81/1.02  --sup_smt_interval                      50000
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Simplification Setup
% 3.81/1.02  
% 3.81/1.02  --sup_indices_passive                   []
% 3.81/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_full_bw                           [BwDemod]
% 3.81/1.02  --sup_immed_triv                        [TrivRules]
% 3.81/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_immed_bw_main                     []
% 3.81/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.02  
% 3.81/1.02  ------ Combination Options
% 3.81/1.02  
% 3.81/1.02  --comb_res_mult                         3
% 3.81/1.02  --comb_sup_mult                         2
% 3.81/1.02  --comb_inst_mult                        10
% 3.81/1.02  
% 3.81/1.02  ------ Debug Options
% 3.81/1.02  
% 3.81/1.02  --dbg_backtrace                         false
% 3.81/1.02  --dbg_dump_prop_clauses                 false
% 3.81/1.02  --dbg_dump_prop_clauses_file            -
% 3.81/1.02  --dbg_out_stat                          false
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  ------ Proving...
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  % SZS status Theorem for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02   Resolution empty clause
% 3.81/1.02  
% 3.81/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  fof(f1,axiom,(
% 3.81/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f28,plain,(
% 3.81/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f1])).
% 3.81/1.02  
% 3.81/1.02  fof(f9,axiom,(
% 3.81/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f13,plain,(
% 3.81/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.81/1.02    inference(unused_predicate_definition_removal,[],[f9])).
% 3.81/1.02  
% 3.81/1.02  fof(f19,plain,(
% 3.81/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.81/1.02    inference(ennf_transformation,[],[f13])).
% 3.81/1.02  
% 3.81/1.02  fof(f36,plain,(
% 3.81/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f19])).
% 3.81/1.02  
% 3.81/1.02  fof(f5,axiom,(
% 3.81/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f16,plain,(
% 3.81/1.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f5])).
% 3.81/1.02  
% 3.81/1.02  fof(f32,plain,(
% 3.81/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f16])).
% 3.81/1.02  
% 3.81/1.02  fof(f3,axiom,(
% 3.81/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f14,plain,(
% 3.81/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f3])).
% 3.81/1.02  
% 3.81/1.02  fof(f30,plain,(
% 3.81/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f14])).
% 3.81/1.02  
% 3.81/1.02  fof(f8,axiom,(
% 3.81/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f35,plain,(
% 3.81/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f8])).
% 3.81/1.02  
% 3.81/1.02  fof(f2,axiom,(
% 3.81/1.02    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f29,plain,(
% 3.81/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f2])).
% 3.81/1.02  
% 3.81/1.02  fof(f44,plain,(
% 3.81/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.81/1.02    inference(definition_unfolding,[],[f35,f29])).
% 3.81/1.02  
% 3.81/1.02  fof(f11,conjecture,(
% 3.81/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f12,negated_conjecture,(
% 3.81/1.02    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.81/1.02    inference(negated_conjecture,[],[f11])).
% 3.81/1.02  
% 3.81/1.02  fof(f22,plain,(
% 3.81/1.02    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.81/1.02    inference(ennf_transformation,[],[f12])).
% 3.81/1.02  
% 3.81/1.02  fof(f23,plain,(
% 3.81/1.02    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.81/1.02    inference(flattening,[],[f22])).
% 3.81/1.02  
% 3.81/1.02  fof(f26,plain,(
% 3.81/1.02    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f25,plain,(
% 3.81/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v1_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f24,plain,(
% 3.81/1.02    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f27,plain,(
% 3.81/1.02    ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 3.81/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).
% 3.81/1.02  
% 3.81/1.02  fof(f39,plain,(
% 3.81/1.02    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.81/1.02    inference(cnf_transformation,[],[f27])).
% 3.81/1.02  
% 3.81/1.02  fof(f6,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f17,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f6])).
% 3.81/1.02  
% 3.81/1.02  fof(f33,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f17])).
% 3.81/1.02  
% 3.81/1.02  fof(f4,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f15,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f4])).
% 3.81/1.02  
% 3.81/1.02  fof(f31,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f15])).
% 3.81/1.02  
% 3.81/1.02  fof(f7,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f18,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f7])).
% 3.81/1.02  
% 3.81/1.02  fof(f34,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f18])).
% 3.81/1.02  
% 3.81/1.02  fof(f43,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(definition_unfolding,[],[f34,f29])).
% 3.81/1.02  
% 3.81/1.02  fof(f10,axiom,(
% 3.81/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.81/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f20,plain,(
% 3.81/1.02    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.81/1.02    inference(ennf_transformation,[],[f10])).
% 3.81/1.02  
% 3.81/1.02  fof(f21,plain,(
% 3.81/1.02    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.81/1.02    inference(flattening,[],[f20])).
% 3.81/1.02  
% 3.81/1.02  fof(f37,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f21])).
% 3.81/1.02  
% 3.81/1.02  fof(f38,plain,(
% 3.81/1.02    l1_pre_topc(sK0)),
% 3.81/1.02    inference(cnf_transformation,[],[f27])).
% 3.81/1.02  
% 3.81/1.02  fof(f41,plain,(
% 3.81/1.02    v1_tops_2(sK1,sK0)),
% 3.81/1.02    inference(cnf_transformation,[],[f27])).
% 3.81/1.02  
% 3.81/1.02  fof(f42,plain,(
% 3.81/1.02    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 3.81/1.02    inference(cnf_transformation,[],[f27])).
% 3.81/1.02  
% 3.81/1.02  cnf(c_0,plain,
% 3.81/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f28]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_7,plain,
% 3.81/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_155,plain,
% 3.81/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | X1 != X2 | k4_xboole_0(X2,X3) != X0 ),
% 3.81/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_156,plain,
% 3.81/1.02      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
% 3.81/1.02      inference(unflattening,[status(thm)],[c_155]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_273,plain,
% 3.81/1.02      ( m1_subset_1(k4_xboole_0(X0_43,X1_43),k1_zfmisc_1(X0_43)) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_156]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_521,plain,
% 3.81/1.02      ( m1_subset_1(k4_xboole_0(X0_43,X1_43),k1_zfmisc_1(X0_43)) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/1.02      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.81/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_281,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.81/1.02      | k3_subset_1(X1_43,k3_subset_1(X1_43,X0_43)) = X0_43 ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_514,plain,
% 3.81/1.02      ( k3_subset_1(X0_43,k3_subset_1(X0_43,X1_43)) = X1_43
% 3.81/1.02      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1034,plain,
% 3.81/1.02      ( k3_subset_1(X0_43,k3_subset_1(X0_43,k4_xboole_0(X0_43,X1_43))) = k4_xboole_0(X0_43,X1_43) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_521,c_514]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/1.02      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f30]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_283,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.81/1.02      | k3_subset_1(X1_43,X0_43) = k4_xboole_0(X1_43,X0_43) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_512,plain,
% 3.81/1.02      ( k3_subset_1(X0_43,X1_43) = k4_xboole_0(X0_43,X1_43)
% 3.81/1.02      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_895,plain,
% 3.81/1.02      ( k3_subset_1(X0_43,k4_xboole_0(X0_43,X1_43)) = k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_521,c_512]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_6,plain,
% 3.81/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.81/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_278,plain,
% 3.81/1.02      ( k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) = k1_setfam_1(k2_tarski(X0_43,X1_43)) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_900,plain,
% 3.81/1.02      ( k3_subset_1(X0_43,k4_xboole_0(X0_43,X1_43)) = k1_setfam_1(k2_tarski(X0_43,X1_43)) ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_895,c_278]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_909,plain,
% 3.81/1.02      ( k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(X0_43,X1_43))) = k3_subset_1(X0_43,k1_setfam_1(k2_tarski(X0_43,X1_43))) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_278,c_900]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1040,plain,
% 3.81/1.02      ( k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(X0_43,X1_43))) = k4_xboole_0(X0_43,X1_43) ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_1034,c_900,c_909]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_12,negated_conjecture,
% 3.81/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.81/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_274,negated_conjecture,
% 3.81/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_520,plain,
% 3.81/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/1.02      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.81/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_280,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.81/1.02      | k7_subset_1(X1_43,X0_43,X2_43) = k4_xboole_0(X0_43,X2_43) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_515,plain,
% 3.81/1.02      ( k7_subset_1(X0_43,X1_43,X2_43) = k4_xboole_0(X1_43,X2_43)
% 3.81/1.02      | m1_subset_1(X1_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1753,plain,
% 3.81/1.02      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_43) = k4_xboole_0(sK1,X0_43) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_520,c_515]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/1.02      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 3.81/1.02      inference(cnf_transformation,[],[f31]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_282,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.81/1.02      | m1_subset_1(k7_subset_1(X1_43,X0_43,X2_43),k1_zfmisc_1(X1_43)) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_513,plain,
% 3.81/1.02      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 3.81/1.02      | m1_subset_1(k7_subset_1(X1_43,X0_43,X2_43),k1_zfmisc_1(X1_43)) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2065,plain,
% 3.81/1.02      ( m1_subset_1(k4_xboole_0(sK1,X0_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.81/1.02      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_1753,c_513]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_15,plain,
% 3.81/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2356,plain,
% 3.81/1.02      ( m1_subset_1(k4_xboole_0(sK1,X0_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.81/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2065,c_15]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_5,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/1.02      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_279,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.81/1.02      | k4_xboole_0(X2_43,k4_xboole_0(X2_43,X0_43)) = k9_subset_1(X1_43,X2_43,X0_43) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_516,plain,
% 3.81/1.02      ( k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) = k9_subset_1(X2_43,X0_43,X1_43)
% 3.81/1.02      | m1_subset_1(X1_43,k1_zfmisc_1(X2_43)) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_551,plain,
% 3.81/1.02      ( k9_subset_1(X0_43,X1_43,X2_43) = k1_setfam_1(k2_tarski(X1_43,X2_43))
% 3.81/1.02      | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_516,c_278]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2370,plain,
% 3.81/1.02      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_43,k4_xboole_0(sK1,X1_43)) = k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(sK1,X1_43))) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_2356,c_551]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_8,plain,
% 3.81/1.02      ( ~ v1_tops_2(X0,X1)
% 3.81/1.02      | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X0,X2),X1)
% 3.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.81/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.81/1.02      | ~ l1_pre_topc(X1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_13,negated_conjecture,
% 3.81/1.02      ( l1_pre_topc(sK0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_166,plain,
% 3.81/1.02      ( ~ v1_tops_2(X0,X1)
% 3.81/1.02      | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X0,X2),X1)
% 3.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.81/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.81/1.02      | sK0 != X1 ),
% 3.81/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_167,plain,
% 3.81/1.02      ( ~ v1_tops_2(X0,sK0)
% 3.81/1.02      | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0,X1),sK0)
% 3.81/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.81/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.81/1.02      inference(unflattening,[status(thm)],[c_166]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_272,plain,
% 3.81/1.02      ( ~ v1_tops_2(X0_43,sK0)
% 3.81/1.02      | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_43,X1_43),sK0)
% 3.81/1.02      | ~ m1_subset_1(X0_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.81/1.02      | ~ m1_subset_1(X1_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_167]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_522,plain,
% 3.81/1.02      ( v1_tops_2(X0_43,sK0) != iProver_top
% 3.81/1.02      | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_43,X1_43),sK0) = iProver_top
% 3.81/1.02      | m1_subset_1(X0_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.81/1.02      | m1_subset_1(X1_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4081,plain,
% 3.81/1.02      ( v1_tops_2(X0_43,sK0) != iProver_top
% 3.81/1.02      | v1_tops_2(k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(sK1,X1_43))),sK0) = iProver_top
% 3.81/1.02      | m1_subset_1(X0_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.81/1.02      | m1_subset_1(k4_xboole_0(sK1,X1_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_2370,c_522]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4103,plain,
% 3.81/1.02      ( v1_tops_2(X0_43,sK0) != iProver_top
% 3.81/1.02      | v1_tops_2(k1_setfam_1(k2_tarski(X0_43,k4_xboole_0(sK1,X1_43))),sK0) = iProver_top
% 3.81/1.02      | m1_subset_1(X0_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.81/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4081,c_2356]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4107,plain,
% 3.81/1.02      ( v1_tops_2(k4_xboole_0(sK1,X0_43),sK0) = iProver_top
% 3.81/1.02      | v1_tops_2(sK1,sK0) != iProver_top
% 3.81/1.02      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_1040,c_4103]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_10,negated_conjecture,
% 3.81/1.02      ( v1_tops_2(sK1,sK0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_17,plain,
% 3.81/1.02      ( v1_tops_2(sK1,sK0) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_12508,plain,
% 3.81/1.02      ( v1_tops_2(k4_xboole_0(sK1,X0_43),sK0) = iProver_top ),
% 3.81/1.02      inference(global_propositional_subsumption,
% 3.81/1.02                [status(thm)],
% 3.81/1.02                [c_4107,c_15,c_17]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_9,negated_conjecture,
% 3.81/1.02      ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_277,negated_conjecture,
% 3.81/1.02      ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_517,plain,
% 3.81/1.02      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2063,plain,
% 3.81/1.02      ( v1_tops_2(k4_xboole_0(sK1,sK2),sK0) != iProver_top ),
% 3.81/1.02      inference(demodulation,[status(thm)],[c_1753,c_517]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_12517,plain,
% 3.81/1.02      ( $false ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_12508,c_2063]) ).
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  ------                               Statistics
% 3.81/1.02  
% 3.81/1.02  ------ General
% 3.81/1.02  
% 3.81/1.02  abstr_ref_over_cycles:                  0
% 3.81/1.02  abstr_ref_under_cycles:                 0
% 3.81/1.02  gc_basic_clause_elim:                   0
% 3.81/1.02  forced_gc_time:                         0
% 3.81/1.02  parsing_time:                           0.006
% 3.81/1.02  unif_index_cands_time:                  0.
% 3.81/1.02  unif_index_add_time:                    0.
% 3.81/1.02  orderings_time:                         0.
% 3.81/1.02  out_proof_time:                         0.009
% 3.81/1.02  total_time:                             0.373
% 3.81/1.02  num_of_symbols:                         49
% 3.81/1.02  num_of_terms:                           19577
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing
% 3.81/1.02  
% 3.81/1.02  num_of_splits:                          0
% 3.81/1.02  num_of_split_atoms:                     0
% 3.81/1.02  num_of_reused_defs:                     0
% 3.81/1.02  num_eq_ax_congr_red:                    21
% 3.81/1.02  num_of_sem_filtered_clauses:            1
% 3.81/1.02  num_of_subtypes:                        3
% 3.81/1.02  monotx_restored_types:                  0
% 3.81/1.02  sat_num_of_epr_types:                   0
% 3.81/1.02  sat_num_of_non_cyclic_types:            0
% 3.81/1.02  sat_guarded_non_collapsed_types:        1
% 3.81/1.02  num_pure_diseq_elim:                    0
% 3.81/1.02  simp_replaced_by:                       0
% 3.81/1.02  res_preprocessed:                       73
% 3.81/1.02  prep_upred:                             0
% 3.81/1.02  prep_unflattend:                        3
% 3.81/1.02  smt_new_axioms:                         0
% 3.81/1.02  pred_elim_cands:                        2
% 3.81/1.02  pred_elim:                              2
% 3.81/1.02  pred_elim_cl:                           2
% 3.81/1.02  pred_elim_cycles:                       4
% 3.81/1.02  merged_defs:                            0
% 3.81/1.02  merged_defs_ncl:                        0
% 3.81/1.02  bin_hyper_res:                          0
% 3.81/1.02  prep_cycles:                            4
% 3.81/1.02  pred_elim_time:                         0.001
% 3.81/1.02  splitting_time:                         0.
% 3.81/1.02  sem_filter_time:                        0.
% 3.81/1.02  monotx_time:                            0.
% 3.81/1.02  subtype_inf_time:                       0.
% 3.81/1.02  
% 3.81/1.02  ------ Problem properties
% 3.81/1.02  
% 3.81/1.02  clauses:                                12
% 3.81/1.02  conjectures:                            4
% 3.81/1.02  epr:                                    1
% 3.81/1.02  horn:                                   12
% 3.81/1.02  ground:                                 4
% 3.81/1.02  unary:                                  6
% 3.81/1.02  binary:                                 5
% 3.81/1.02  lits:                                   20
% 3.81/1.02  lits_eq:                                5
% 3.81/1.02  fd_pure:                                0
% 3.81/1.02  fd_pseudo:                              0
% 3.81/1.02  fd_cond:                                0
% 3.81/1.02  fd_pseudo_cond:                         0
% 3.81/1.02  ac_symbols:                             0
% 3.81/1.02  
% 3.81/1.02  ------ Propositional Solver
% 3.81/1.02  
% 3.81/1.02  prop_solver_calls:                      29
% 3.81/1.02  prop_fast_solver_calls:                 520
% 3.81/1.02  smt_solver_calls:                       0
% 3.81/1.02  smt_fast_solver_calls:                  0
% 3.81/1.02  prop_num_of_clauses:                    5091
% 3.81/1.02  prop_preprocess_simplified:             12612
% 3.81/1.02  prop_fo_subsumed:                       13
% 3.81/1.02  prop_solver_time:                       0.
% 3.81/1.02  smt_solver_time:                        0.
% 3.81/1.02  smt_fast_solver_time:                   0.
% 3.81/1.02  prop_fast_solver_time:                  0.
% 3.81/1.02  prop_unsat_core_time:                   0.
% 3.81/1.02  
% 3.81/1.02  ------ QBF
% 3.81/1.02  
% 3.81/1.02  qbf_q_res:                              0
% 3.81/1.02  qbf_num_tautologies:                    0
% 3.81/1.02  qbf_prep_cycles:                        0
% 3.81/1.02  
% 3.81/1.02  ------ BMC1
% 3.81/1.02  
% 3.81/1.02  bmc1_current_bound:                     -1
% 3.81/1.02  bmc1_last_solved_bound:                 -1
% 3.81/1.02  bmc1_unsat_core_size:                   -1
% 3.81/1.02  bmc1_unsat_core_parents_size:           -1
% 3.81/1.02  bmc1_merge_next_fun:                    0
% 3.81/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation
% 3.81/1.02  
% 3.81/1.02  inst_num_of_clauses:                    1700
% 3.81/1.02  inst_num_in_passive:                    1016
% 3.81/1.02  inst_num_in_active:                     613
% 3.81/1.02  inst_num_in_unprocessed:                71
% 3.81/1.02  inst_num_of_loops:                      660
% 3.81/1.02  inst_num_of_learning_restarts:          0
% 3.81/1.02  inst_num_moves_active_passive:          44
% 3.81/1.02  inst_lit_activity:                      0
% 3.81/1.02  inst_lit_activity_moves:                0
% 3.81/1.02  inst_num_tautologies:                   0
% 3.81/1.02  inst_num_prop_implied:                  0
% 3.81/1.02  inst_num_existing_simplified:           0
% 3.81/1.02  inst_num_eq_res_simplified:             0
% 3.81/1.02  inst_num_child_elim:                    0
% 3.81/1.02  inst_num_of_dismatching_blockings:      1064
% 3.81/1.02  inst_num_of_non_proper_insts:           1677
% 3.81/1.02  inst_num_of_duplicates:                 0
% 3.81/1.02  inst_inst_num_from_inst_to_res:         0
% 3.81/1.02  inst_dismatching_checking_time:         0.
% 3.81/1.02  
% 3.81/1.02  ------ Resolution
% 3.81/1.02  
% 3.81/1.02  res_num_of_clauses:                     0
% 3.81/1.02  res_num_in_passive:                     0
% 3.81/1.02  res_num_in_active:                      0
% 3.81/1.02  res_num_of_loops:                       77
% 3.81/1.02  res_forward_subset_subsumed:            146
% 3.81/1.02  res_backward_subset_subsumed:           22
% 3.81/1.02  res_forward_subsumed:                   0
% 3.81/1.02  res_backward_subsumed:                  0
% 3.81/1.02  res_forward_subsumption_resolution:     0
% 3.81/1.02  res_backward_subsumption_resolution:    0
% 3.81/1.02  res_clause_to_clause_subsumption:       593
% 3.81/1.02  res_orphan_elimination:                 0
% 3.81/1.02  res_tautology_del:                      244
% 3.81/1.02  res_num_eq_res_simplified:              0
% 3.81/1.02  res_num_sel_changes:                    0
% 3.81/1.02  res_moves_from_active_to_pass:          0
% 3.81/1.02  
% 3.81/1.02  ------ Superposition
% 3.81/1.02  
% 3.81/1.02  sup_time_total:                         0.
% 3.81/1.02  sup_time_generating:                    0.
% 3.81/1.02  sup_time_sim_full:                      0.
% 3.81/1.02  sup_time_sim_immed:                     0.
% 3.81/1.02  
% 3.81/1.02  sup_num_of_clauses:                     241
% 3.81/1.02  sup_num_in_active:                      122
% 3.81/1.02  sup_num_in_passive:                     119
% 3.81/1.02  sup_num_of_loops:                       130
% 3.81/1.02  sup_fw_superposition:                   394
% 3.81/1.02  sup_bw_superposition:                   213
% 3.81/1.02  sup_immediate_simplified:               435
% 3.81/1.02  sup_given_eliminated:                   0
% 3.81/1.02  comparisons_done:                       0
% 3.81/1.02  comparisons_avoided:                    0
% 3.81/1.02  
% 3.81/1.02  ------ Simplifications
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  sim_fw_subset_subsumed:                 9
% 3.81/1.02  sim_bw_subset_subsumed:                 19
% 3.81/1.02  sim_fw_subsumed:                        67
% 3.81/1.02  sim_bw_subsumed:                        8
% 3.81/1.02  sim_fw_subsumption_res:                 3
% 3.81/1.02  sim_bw_subsumption_res:                 0
% 3.81/1.02  sim_tautology_del:                      0
% 3.81/1.02  sim_eq_tautology_del:                   89
% 3.81/1.02  sim_eq_res_simp:                        0
% 3.81/1.02  sim_fw_demodulated:                     168
% 3.81/1.02  sim_bw_demodulated:                     9
% 3.81/1.02  sim_light_normalised:                   230
% 3.81/1.02  sim_joinable_taut:                      0
% 3.81/1.02  sim_joinable_simp:                      0
% 3.81/1.02  sim_ac_normalised:                      0
% 3.81/1.02  sim_smt_subsumption:                    0
% 3.81/1.02  
%------------------------------------------------------------------------------
