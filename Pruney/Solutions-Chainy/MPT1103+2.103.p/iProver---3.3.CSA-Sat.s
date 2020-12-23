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
% DateTime   : Thu Dec  3 12:11:04 EST 2020

% Result     : CounterSatisfiable 1.93s
% Output     : Saturation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 407 expanded)
%              Number of clauses        :   46 ( 136 expanded)
%              Number of leaves         :   16 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 888 expanded)
%              Number of equality atoms :  104 ( 559 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f22,f28])).

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

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_114,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_107,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_328,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_1,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_122,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k1_setfam_1(k2_tarski(X2,X3)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_123,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_512,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123])).

cnf(c_873,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_512])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_514,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1136,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = k7_subset_1(X1,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_873,c_514])).

cnf(c_1445,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(X2,k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1136,c_1136])).

cnf(c_1134,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2))) = k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_512,c_514])).

cnf(c_1327,plain,
    ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),k1_xboole_0) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_1134])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1335,plain,
    ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),k1_xboole_0) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1327,c_2])).

cnf(c_1340,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1,c_1335])).

cnf(c_1341,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1340,c_1])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_515,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_524,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_515,c_3])).

cnf(c_1135,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_524,c_514])).

cnf(c_1329,plain,
    ( k7_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1)),X2) = k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1134,c_1135])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_513,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1133,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_513,c_514])).

cnf(c_1161,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1133,c_1135])).

cnf(c_1153,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_1135])).

cnf(c_1155,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1153,c_2])).

cnf(c_1140,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1135,c_514])).

cnf(c_8,negated_conjecture,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_133,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_511,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_604,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_513,c_511])).

cnf(c_691,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_8,c_604])).

cnf(c_957,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_873,c_511])).

cnf(c_1027,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_691,c_957])).

cnf(c_954,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_524,c_511])).

cnf(c_742,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)) ),
    inference(superposition,[status(thm)],[c_512,c_511])).

cnf(c_11,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.93/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.01  
% 1.93/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/1.01  
% 1.93/1.01  ------  iProver source info
% 1.93/1.01  
% 1.93/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.93/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/1.01  git: non_committed_changes: false
% 1.93/1.01  git: last_make_outside_of_git: false
% 1.93/1.01  
% 1.93/1.01  ------ 
% 1.93/1.01  
% 1.93/1.01  ------ Input Options
% 1.93/1.01  
% 1.93/1.01  --out_options                           all
% 1.93/1.01  --tptp_safe_out                         true
% 1.93/1.01  --problem_path                          ""
% 1.93/1.01  --include_path                          ""
% 1.93/1.01  --clausifier                            res/vclausify_rel
% 1.93/1.01  --clausifier_options                    --mode clausify
% 1.93/1.01  --stdin                                 false
% 1.93/1.01  --stats_out                             all
% 1.93/1.01  
% 1.93/1.01  ------ General Options
% 1.93/1.01  
% 1.93/1.01  --fof                                   false
% 1.93/1.01  --time_out_real                         305.
% 1.93/1.01  --time_out_virtual                      -1.
% 1.93/1.01  --symbol_type_check                     false
% 1.93/1.01  --clausify_out                          false
% 1.93/1.01  --sig_cnt_out                           false
% 1.93/1.01  --trig_cnt_out                          false
% 1.93/1.01  --trig_cnt_out_tolerance                1.
% 1.93/1.01  --trig_cnt_out_sk_spl                   false
% 1.93/1.01  --abstr_cl_out                          false
% 1.93/1.01  
% 1.93/1.01  ------ Global Options
% 1.93/1.01  
% 1.93/1.01  --schedule                              default
% 1.93/1.01  --add_important_lit                     false
% 1.93/1.01  --prop_solver_per_cl                    1000
% 1.93/1.01  --min_unsat_core                        false
% 1.93/1.01  --soft_assumptions                      false
% 1.93/1.01  --soft_lemma_size                       3
% 1.93/1.01  --prop_impl_unit_size                   0
% 1.93/1.01  --prop_impl_unit                        []
% 1.93/1.01  --share_sel_clauses                     true
% 1.93/1.01  --reset_solvers                         false
% 1.93/1.01  --bc_imp_inh                            [conj_cone]
% 1.93/1.01  --conj_cone_tolerance                   3.
% 1.93/1.01  --extra_neg_conj                        none
% 1.93/1.01  --large_theory_mode                     true
% 1.93/1.01  --prolific_symb_bound                   200
% 1.93/1.01  --lt_threshold                          2000
% 1.93/1.01  --clause_weak_htbl                      true
% 1.93/1.01  --gc_record_bc_elim                     false
% 1.93/1.01  
% 1.93/1.01  ------ Preprocessing Options
% 1.93/1.01  
% 1.93/1.01  --preprocessing_flag                    true
% 1.93/1.01  --time_out_prep_mult                    0.1
% 1.93/1.01  --splitting_mode                        input
% 1.93/1.01  --splitting_grd                         true
% 1.93/1.01  --splitting_cvd                         false
% 1.93/1.01  --splitting_cvd_svl                     false
% 1.93/1.01  --splitting_nvd                         32
% 1.93/1.01  --sub_typing                            true
% 1.93/1.01  --prep_gs_sim                           true
% 1.93/1.01  --prep_unflatten                        true
% 1.93/1.01  --prep_res_sim                          true
% 1.93/1.01  --prep_upred                            true
% 1.93/1.01  --prep_sem_filter                       exhaustive
% 1.93/1.01  --prep_sem_filter_out                   false
% 1.93/1.01  --pred_elim                             true
% 1.93/1.01  --res_sim_input                         true
% 1.93/1.01  --eq_ax_congr_red                       true
% 1.93/1.01  --pure_diseq_elim                       true
% 1.93/1.01  --brand_transform                       false
% 1.93/1.01  --non_eq_to_eq                          false
% 1.93/1.01  --prep_def_merge                        true
% 1.93/1.01  --prep_def_merge_prop_impl              false
% 1.93/1.01  --prep_def_merge_mbd                    true
% 1.93/1.01  --prep_def_merge_tr_red                 false
% 1.93/1.01  --prep_def_merge_tr_cl                  false
% 1.93/1.01  --smt_preprocessing                     true
% 1.93/1.01  --smt_ac_axioms                         fast
% 1.93/1.01  --preprocessed_out                      false
% 1.93/1.01  --preprocessed_stats                    false
% 1.93/1.01  
% 1.93/1.01  ------ Abstraction refinement Options
% 1.93/1.01  
% 1.93/1.01  --abstr_ref                             []
% 1.93/1.01  --abstr_ref_prep                        false
% 1.93/1.01  --abstr_ref_until_sat                   false
% 1.93/1.01  --abstr_ref_sig_restrict                funpre
% 1.93/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/1.01  --abstr_ref_under                       []
% 1.93/1.01  
% 1.93/1.01  ------ SAT Options
% 1.93/1.01  
% 1.93/1.01  --sat_mode                              false
% 1.93/1.01  --sat_fm_restart_options                ""
% 1.93/1.01  --sat_gr_def                            false
% 1.93/1.01  --sat_epr_types                         true
% 1.93/1.01  --sat_non_cyclic_types                  false
% 1.93/1.01  --sat_finite_models                     false
% 1.93/1.01  --sat_fm_lemmas                         false
% 1.93/1.01  --sat_fm_prep                           false
% 1.93/1.02  --sat_fm_uc_incr                        true
% 1.93/1.02  --sat_out_model                         small
% 1.93/1.02  --sat_out_clauses                       false
% 1.93/1.02  
% 1.93/1.02  ------ QBF Options
% 1.93/1.02  
% 1.93/1.02  --qbf_mode                              false
% 1.93/1.02  --qbf_elim_univ                         false
% 1.93/1.02  --qbf_dom_inst                          none
% 1.93/1.02  --qbf_dom_pre_inst                      false
% 1.93/1.02  --qbf_sk_in                             false
% 1.93/1.02  --qbf_pred_elim                         true
% 1.93/1.02  --qbf_split                             512
% 1.93/1.02  
% 1.93/1.02  ------ BMC1 Options
% 1.93/1.02  
% 1.93/1.02  --bmc1_incremental                      false
% 1.93/1.02  --bmc1_axioms                           reachable_all
% 1.93/1.02  --bmc1_min_bound                        0
% 1.93/1.02  --bmc1_max_bound                        -1
% 1.93/1.02  --bmc1_max_bound_default                -1
% 1.93/1.02  --bmc1_symbol_reachability              true
% 1.93/1.02  --bmc1_property_lemmas                  false
% 1.93/1.02  --bmc1_k_induction                      false
% 1.93/1.02  --bmc1_non_equiv_states                 false
% 1.93/1.02  --bmc1_deadlock                         false
% 1.93/1.02  --bmc1_ucm                              false
% 1.93/1.02  --bmc1_add_unsat_core                   none
% 1.93/1.02  --bmc1_unsat_core_children              false
% 1.93/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/1.02  --bmc1_out_stat                         full
% 1.93/1.02  --bmc1_ground_init                      false
% 1.93/1.02  --bmc1_pre_inst_next_state              false
% 1.93/1.02  --bmc1_pre_inst_state                   false
% 1.93/1.02  --bmc1_pre_inst_reach_state             false
% 1.93/1.02  --bmc1_out_unsat_core                   false
% 1.93/1.02  --bmc1_aig_witness_out                  false
% 1.93/1.02  --bmc1_verbose                          false
% 1.93/1.02  --bmc1_dump_clauses_tptp                false
% 1.93/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.93/1.02  --bmc1_dump_file                        -
% 1.93/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.93/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.93/1.02  --bmc1_ucm_extend_mode                  1
% 1.93/1.02  --bmc1_ucm_init_mode                    2
% 1.93/1.02  --bmc1_ucm_cone_mode                    none
% 1.93/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.93/1.02  --bmc1_ucm_relax_model                  4
% 1.93/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.93/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/1.02  --bmc1_ucm_layered_model                none
% 1.93/1.02  --bmc1_ucm_max_lemma_size               10
% 1.93/1.02  
% 1.93/1.02  ------ AIG Options
% 1.93/1.02  
% 1.93/1.02  --aig_mode                              false
% 1.93/1.02  
% 1.93/1.02  ------ Instantiation Options
% 1.93/1.02  
% 1.93/1.02  --instantiation_flag                    true
% 1.93/1.02  --inst_sos_flag                         false
% 1.93/1.02  --inst_sos_phase                        true
% 1.93/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/1.02  --inst_lit_sel_side                     num_symb
% 1.93/1.02  --inst_solver_per_active                1400
% 1.93/1.02  --inst_solver_calls_frac                1.
% 1.93/1.02  --inst_passive_queue_type               priority_queues
% 1.93/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/1.02  --inst_passive_queues_freq              [25;2]
% 1.93/1.02  --inst_dismatching                      true
% 1.93/1.02  --inst_eager_unprocessed_to_passive     true
% 1.93/1.02  --inst_prop_sim_given                   true
% 1.93/1.02  --inst_prop_sim_new                     false
% 1.93/1.02  --inst_subs_new                         false
% 1.93/1.02  --inst_eq_res_simp                      false
% 1.93/1.02  --inst_subs_given                       false
% 1.93/1.02  --inst_orphan_elimination               true
% 1.93/1.02  --inst_learning_loop_flag               true
% 1.93/1.02  --inst_learning_start                   3000
% 1.93/1.02  --inst_learning_factor                  2
% 1.93/1.02  --inst_start_prop_sim_after_learn       3
% 1.93/1.02  --inst_sel_renew                        solver
% 1.93/1.02  --inst_lit_activity_flag                true
% 1.93/1.02  --inst_restr_to_given                   false
% 1.93/1.02  --inst_activity_threshold               500
% 1.93/1.02  --inst_out_proof                        true
% 1.93/1.02  
% 1.93/1.02  ------ Resolution Options
% 1.93/1.02  
% 1.93/1.02  --resolution_flag                       true
% 1.93/1.02  --res_lit_sel                           adaptive
% 1.93/1.02  --res_lit_sel_side                      none
% 1.93/1.02  --res_ordering                          kbo
% 1.93/1.02  --res_to_prop_solver                    active
% 1.93/1.02  --res_prop_simpl_new                    false
% 1.93/1.02  --res_prop_simpl_given                  true
% 1.93/1.02  --res_passive_queue_type                priority_queues
% 1.93/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/1.02  --res_passive_queues_freq               [15;5]
% 1.93/1.02  --res_forward_subs                      full
% 1.93/1.02  --res_backward_subs                     full
% 1.93/1.02  --res_forward_subs_resolution           true
% 1.93/1.02  --res_backward_subs_resolution          true
% 1.93/1.02  --res_orphan_elimination                true
% 1.93/1.02  --res_time_limit                        2.
% 1.93/1.02  --res_out_proof                         true
% 1.93/1.02  
% 1.93/1.02  ------ Superposition Options
% 1.93/1.02  
% 1.93/1.02  --superposition_flag                    true
% 1.93/1.02  --sup_passive_queue_type                priority_queues
% 1.93/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.93/1.02  --demod_completeness_check              fast
% 1.93/1.02  --demod_use_ground                      true
% 1.93/1.02  --sup_to_prop_solver                    passive
% 1.93/1.02  --sup_prop_simpl_new                    true
% 1.93/1.02  --sup_prop_simpl_given                  true
% 1.93/1.02  --sup_fun_splitting                     false
% 1.93/1.02  --sup_smt_interval                      50000
% 1.93/1.02  
% 1.93/1.02  ------ Superposition Simplification Setup
% 1.93/1.02  
% 1.93/1.02  --sup_indices_passive                   []
% 1.93/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.02  --sup_full_bw                           [BwDemod]
% 1.93/1.02  --sup_immed_triv                        [TrivRules]
% 1.93/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.02  --sup_immed_bw_main                     []
% 1.93/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/1.02  
% 1.93/1.02  ------ Combination Options
% 1.93/1.02  
% 1.93/1.02  --comb_res_mult                         3
% 1.93/1.02  --comb_sup_mult                         2
% 1.93/1.02  --comb_inst_mult                        10
% 1.93/1.02  
% 1.93/1.02  ------ Debug Options
% 1.93/1.02  
% 1.93/1.02  --dbg_backtrace                         false
% 1.93/1.02  --dbg_dump_prop_clauses                 false
% 1.93/1.02  --dbg_dump_prop_clauses_file            -
% 1.93/1.02  --dbg_out_stat                          false
% 1.93/1.02  ------ Parsing...
% 1.93/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.93/1.02  
% 1.93/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.93/1.02  
% 1.93/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.93/1.02  
% 1.93/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.93/1.02  ------ Proving...
% 1.93/1.02  ------ Problem Properties 
% 1.93/1.02  
% 1.93/1.02  
% 1.93/1.02  clauses                                 10
% 1.93/1.02  conjectures                             3
% 1.93/1.02  EPR                                     0
% 1.93/1.02  Horn                                    9
% 1.93/1.02  unary                                   6
% 1.93/1.02  binary                                  4
% 1.93/1.02  lits                                    14
% 1.93/1.02  lits eq                                 9
% 1.93/1.02  fd_pure                                 0
% 1.93/1.02  fd_pseudo                               0
% 1.93/1.02  fd_cond                                 0
% 1.93/1.02  fd_pseudo_cond                          0
% 1.93/1.02  AC symbols                              0
% 1.93/1.02  
% 1.93/1.02  ------ Schedule dynamic 5 is on 
% 1.93/1.02  
% 1.93/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.93/1.02  
% 1.93/1.02  
% 1.93/1.02  ------ 
% 1.93/1.02  Current options:
% 1.93/1.02  ------ 
% 1.93/1.02  
% 1.93/1.02  ------ Input Options
% 1.93/1.02  
% 1.93/1.02  --out_options                           all
% 1.93/1.02  --tptp_safe_out                         true
% 1.93/1.02  --problem_path                          ""
% 1.93/1.02  --include_path                          ""
% 1.93/1.02  --clausifier                            res/vclausify_rel
% 1.93/1.02  --clausifier_options                    --mode clausify
% 1.93/1.02  --stdin                                 false
% 1.93/1.02  --stats_out                             all
% 1.93/1.02  
% 1.93/1.02  ------ General Options
% 1.93/1.02  
% 1.93/1.02  --fof                                   false
% 1.93/1.02  --time_out_real                         305.
% 1.93/1.02  --time_out_virtual                      -1.
% 1.93/1.02  --symbol_type_check                     false
% 1.93/1.02  --clausify_out                          false
% 1.93/1.02  --sig_cnt_out                           false
% 1.93/1.02  --trig_cnt_out                          false
% 1.93/1.02  --trig_cnt_out_tolerance                1.
% 1.93/1.02  --trig_cnt_out_sk_spl                   false
% 1.93/1.02  --abstr_cl_out                          false
% 1.93/1.02  
% 1.93/1.02  ------ Global Options
% 1.93/1.02  
% 1.93/1.02  --schedule                              default
% 1.93/1.02  --add_important_lit                     false
% 1.93/1.02  --prop_solver_per_cl                    1000
% 1.93/1.02  --min_unsat_core                        false
% 1.93/1.02  --soft_assumptions                      false
% 1.93/1.02  --soft_lemma_size                       3
% 1.93/1.02  --prop_impl_unit_size                   0
% 1.93/1.02  --prop_impl_unit                        []
% 1.93/1.02  --share_sel_clauses                     true
% 1.93/1.02  --reset_solvers                         false
% 1.93/1.02  --bc_imp_inh                            [conj_cone]
% 1.93/1.02  --conj_cone_tolerance                   3.
% 1.93/1.02  --extra_neg_conj                        none
% 1.93/1.02  --large_theory_mode                     true
% 1.93/1.02  --prolific_symb_bound                   200
% 1.93/1.02  --lt_threshold                          2000
% 1.93/1.02  --clause_weak_htbl                      true
% 1.93/1.02  --gc_record_bc_elim                     false
% 1.93/1.02  
% 1.93/1.02  ------ Preprocessing Options
% 1.93/1.02  
% 1.93/1.02  --preprocessing_flag                    true
% 1.93/1.02  --time_out_prep_mult                    0.1
% 1.93/1.02  --splitting_mode                        input
% 1.93/1.02  --splitting_grd                         true
% 1.93/1.02  --splitting_cvd                         false
% 1.93/1.02  --splitting_cvd_svl                     false
% 1.93/1.02  --splitting_nvd                         32
% 1.93/1.02  --sub_typing                            true
% 1.93/1.02  --prep_gs_sim                           true
% 1.93/1.02  --prep_unflatten                        true
% 1.93/1.02  --prep_res_sim                          true
% 1.93/1.02  --prep_upred                            true
% 1.93/1.02  --prep_sem_filter                       exhaustive
% 1.93/1.02  --prep_sem_filter_out                   false
% 1.93/1.02  --pred_elim                             true
% 1.93/1.02  --res_sim_input                         true
% 1.93/1.02  --eq_ax_congr_red                       true
% 1.93/1.02  --pure_diseq_elim                       true
% 1.93/1.02  --brand_transform                       false
% 1.93/1.02  --non_eq_to_eq                          false
% 1.93/1.02  --prep_def_merge                        true
% 1.93/1.02  --prep_def_merge_prop_impl              false
% 1.93/1.02  --prep_def_merge_mbd                    true
% 1.93/1.02  --prep_def_merge_tr_red                 false
% 1.93/1.02  --prep_def_merge_tr_cl                  false
% 1.93/1.02  --smt_preprocessing                     true
% 1.93/1.02  --smt_ac_axioms                         fast
% 1.93/1.02  --preprocessed_out                      false
% 1.93/1.02  --preprocessed_stats                    false
% 1.93/1.02  
% 1.93/1.02  ------ Abstraction refinement Options
% 1.93/1.02  
% 1.93/1.02  --abstr_ref                             []
% 1.93/1.02  --abstr_ref_prep                        false
% 1.93/1.02  --abstr_ref_until_sat                   false
% 1.93/1.02  --abstr_ref_sig_restrict                funpre
% 1.93/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/1.02  --abstr_ref_under                       []
% 1.93/1.02  
% 1.93/1.02  ------ SAT Options
% 1.93/1.02  
% 1.93/1.02  --sat_mode                              false
% 1.93/1.02  --sat_fm_restart_options                ""
% 1.93/1.02  --sat_gr_def                            false
% 1.93/1.02  --sat_epr_types                         true
% 1.93/1.02  --sat_non_cyclic_types                  false
% 1.93/1.02  --sat_finite_models                     false
% 1.93/1.02  --sat_fm_lemmas                         false
% 1.93/1.02  --sat_fm_prep                           false
% 1.93/1.02  --sat_fm_uc_incr                        true
% 1.93/1.02  --sat_out_model                         small
% 1.93/1.02  --sat_out_clauses                       false
% 1.93/1.02  
% 1.93/1.02  ------ QBF Options
% 1.93/1.02  
% 1.93/1.02  --qbf_mode                              false
% 1.93/1.02  --qbf_elim_univ                         false
% 1.93/1.02  --qbf_dom_inst                          none
% 1.93/1.02  --qbf_dom_pre_inst                      false
% 1.93/1.02  --qbf_sk_in                             false
% 1.93/1.02  --qbf_pred_elim                         true
% 1.93/1.02  --qbf_split                             512
% 1.93/1.02  
% 1.93/1.02  ------ BMC1 Options
% 1.93/1.02  
% 1.93/1.02  --bmc1_incremental                      false
% 1.93/1.02  --bmc1_axioms                           reachable_all
% 1.93/1.02  --bmc1_min_bound                        0
% 1.93/1.02  --bmc1_max_bound                        -1
% 1.93/1.02  --bmc1_max_bound_default                -1
% 1.93/1.02  --bmc1_symbol_reachability              true
% 1.93/1.02  --bmc1_property_lemmas                  false
% 1.93/1.02  --bmc1_k_induction                      false
% 1.93/1.02  --bmc1_non_equiv_states                 false
% 1.93/1.02  --bmc1_deadlock                         false
% 1.93/1.02  --bmc1_ucm                              false
% 1.93/1.02  --bmc1_add_unsat_core                   none
% 1.93/1.02  --bmc1_unsat_core_children              false
% 1.93/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/1.02  --bmc1_out_stat                         full
% 1.93/1.02  --bmc1_ground_init                      false
% 1.93/1.02  --bmc1_pre_inst_next_state              false
% 1.93/1.02  --bmc1_pre_inst_state                   false
% 1.93/1.02  --bmc1_pre_inst_reach_state             false
% 1.93/1.02  --bmc1_out_unsat_core                   false
% 1.93/1.02  --bmc1_aig_witness_out                  false
% 1.93/1.02  --bmc1_verbose                          false
% 1.93/1.02  --bmc1_dump_clauses_tptp                false
% 1.93/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.93/1.02  --bmc1_dump_file                        -
% 1.93/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.93/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.93/1.02  --bmc1_ucm_extend_mode                  1
% 1.93/1.02  --bmc1_ucm_init_mode                    2
% 1.93/1.02  --bmc1_ucm_cone_mode                    none
% 1.93/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.93/1.02  --bmc1_ucm_relax_model                  4
% 1.93/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.93/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/1.02  --bmc1_ucm_layered_model                none
% 1.93/1.02  --bmc1_ucm_max_lemma_size               10
% 1.93/1.02  
% 1.93/1.02  ------ AIG Options
% 1.93/1.02  
% 1.93/1.02  --aig_mode                              false
% 1.93/1.02  
% 1.93/1.02  ------ Instantiation Options
% 1.93/1.02  
% 1.93/1.02  --instantiation_flag                    true
% 1.93/1.02  --inst_sos_flag                         false
% 1.93/1.02  --inst_sos_phase                        true
% 1.93/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/1.02  --inst_lit_sel_side                     none
% 1.93/1.02  --inst_solver_per_active                1400
% 1.93/1.02  --inst_solver_calls_frac                1.
% 1.93/1.02  --inst_passive_queue_type               priority_queues
% 1.93/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/1.02  --inst_passive_queues_freq              [25;2]
% 1.93/1.02  --inst_dismatching                      true
% 1.93/1.02  --inst_eager_unprocessed_to_passive     true
% 1.93/1.02  --inst_prop_sim_given                   true
% 1.93/1.02  --inst_prop_sim_new                     false
% 1.93/1.02  --inst_subs_new                         false
% 1.93/1.02  --inst_eq_res_simp                      false
% 1.93/1.02  --inst_subs_given                       false
% 1.93/1.02  --inst_orphan_elimination               true
% 1.93/1.02  --inst_learning_loop_flag               true
% 1.93/1.02  --inst_learning_start                   3000
% 1.93/1.02  --inst_learning_factor                  2
% 1.93/1.02  --inst_start_prop_sim_after_learn       3
% 1.93/1.02  --inst_sel_renew                        solver
% 1.93/1.02  --inst_lit_activity_flag                true
% 1.93/1.02  --inst_restr_to_given                   false
% 1.93/1.02  --inst_activity_threshold               500
% 1.93/1.02  --inst_out_proof                        true
% 1.93/1.02  
% 1.93/1.02  ------ Resolution Options
% 1.93/1.02  
% 1.93/1.02  --resolution_flag                       false
% 1.93/1.02  --res_lit_sel                           adaptive
% 1.93/1.02  --res_lit_sel_side                      none
% 1.93/1.02  --res_ordering                          kbo
% 1.93/1.02  --res_to_prop_solver                    active
% 1.93/1.02  --res_prop_simpl_new                    false
% 1.93/1.02  --res_prop_simpl_given                  true
% 1.93/1.02  --res_passive_queue_type                priority_queues
% 1.93/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/1.02  --res_passive_queues_freq               [15;5]
% 1.93/1.02  --res_forward_subs                      full
% 1.93/1.02  --res_backward_subs                     full
% 1.93/1.02  --res_forward_subs_resolution           true
% 1.93/1.02  --res_backward_subs_resolution          true
% 1.93/1.02  --res_orphan_elimination                true
% 1.93/1.02  --res_time_limit                        2.
% 1.93/1.02  --res_out_proof                         true
% 1.93/1.02  
% 1.93/1.02  ------ Superposition Options
% 1.93/1.02  
% 1.93/1.02  --superposition_flag                    true
% 1.93/1.02  --sup_passive_queue_type                priority_queues
% 1.93/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.93/1.02  --demod_completeness_check              fast
% 1.93/1.02  --demod_use_ground                      true
% 1.93/1.02  --sup_to_prop_solver                    passive
% 1.93/1.02  --sup_prop_simpl_new                    true
% 1.93/1.02  --sup_prop_simpl_given                  true
% 1.93/1.02  --sup_fun_splitting                     false
% 1.93/1.02  --sup_smt_interval                      50000
% 1.93/1.02  
% 1.93/1.02  ------ Superposition Simplification Setup
% 1.93/1.02  
% 1.93/1.02  --sup_indices_passive                   []
% 1.93/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.02  --sup_full_bw                           [BwDemod]
% 1.93/1.02  --sup_immed_triv                        [TrivRules]
% 1.93/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.02  --sup_immed_bw_main                     []
% 1.93/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/1.02  
% 1.93/1.02  ------ Combination Options
% 1.93/1.02  
% 1.93/1.02  --comb_res_mult                         3
% 1.93/1.02  --comb_sup_mult                         2
% 1.93/1.02  --comb_inst_mult                        10
% 1.93/1.02  
% 1.93/1.02  ------ Debug Options
% 1.93/1.02  
% 1.93/1.02  --dbg_backtrace                         false
% 1.93/1.02  --dbg_dump_prop_clauses                 false
% 1.93/1.02  --dbg_dump_prop_clauses_file            -
% 1.93/1.02  --dbg_out_stat                          false
% 1.93/1.02  
% 1.93/1.02  
% 1.93/1.02  
% 1.93/1.02  
% 1.93/1.02  ------ Proving...
% 1.93/1.02  
% 1.93/1.02  
% 1.93/1.02  % SZS status CounterSatisfiable for theBenchmark.p
% 1.93/1.02  
% 1.93/1.02  % SZS output start Saturation for theBenchmark.p
% 1.93/1.02  
% 1.93/1.02  fof(f3,axiom,(
% 1.93/1.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f23,plain,(
% 1.93/1.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.93/1.02    inference(cnf_transformation,[],[f3])).
% 1.93/1.02  
% 1.93/1.02  fof(f8,axiom,(
% 1.93/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f28,plain,(
% 1.93/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.93/1.02    inference(cnf_transformation,[],[f8])).
% 1.93/1.02  
% 1.93/1.02  fof(f39,plain,(
% 1.93/1.02    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.93/1.02    inference(definition_unfolding,[],[f23,f28])).
% 1.93/1.02  
% 1.93/1.02  fof(f2,axiom,(
% 1.93/1.02    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f22,plain,(
% 1.93/1.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.93/1.02    inference(cnf_transformation,[],[f2])).
% 1.93/1.02  
% 1.93/1.02  fof(f38,plain,(
% 1.93/1.02    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.93/1.02    inference(definition_unfolding,[],[f22,f28])).
% 1.93/1.02  
% 1.93/1.02  fof(f9,axiom,(
% 1.93/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f13,plain,(
% 1.93/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.93/1.02    inference(unused_predicate_definition_removal,[],[f9])).
% 1.93/1.02  
% 1.93/1.02  fof(f15,plain,(
% 1.93/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.93/1.02    inference(ennf_transformation,[],[f13])).
% 1.93/1.02  
% 1.93/1.02  fof(f29,plain,(
% 1.93/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.93/1.02    inference(cnf_transformation,[],[f15])).
% 1.93/1.02  
% 1.93/1.02  fof(f7,axiom,(
% 1.93/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f14,plain,(
% 1.93/1.02    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/1.02    inference(ennf_transformation,[],[f7])).
% 1.93/1.02  
% 1.93/1.02  fof(f27,plain,(
% 1.93/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.93/1.02    inference(cnf_transformation,[],[f14])).
% 1.93/1.02  
% 1.93/1.02  fof(f1,axiom,(
% 1.93/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f21,plain,(
% 1.93/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.93/1.02    inference(cnf_transformation,[],[f1])).
% 1.93/1.02  
% 1.93/1.02  fof(f37,plain,(
% 1.93/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.93/1.02    inference(definition_unfolding,[],[f21,f28])).
% 1.93/1.02  
% 1.93/1.02  fof(f40,plain,(
% 1.93/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.93/1.02    inference(definition_unfolding,[],[f27,f37])).
% 1.93/1.02  
% 1.93/1.02  fof(f4,axiom,(
% 1.93/1.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f24,plain,(
% 1.93/1.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.93/1.02    inference(cnf_transformation,[],[f4])).
% 1.93/1.02  
% 1.93/1.02  fof(f6,axiom,(
% 1.93/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f26,plain,(
% 1.93/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.93/1.02    inference(cnf_transformation,[],[f6])).
% 1.93/1.02  
% 1.93/1.02  fof(f5,axiom,(
% 1.93/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f25,plain,(
% 1.93/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.93/1.02    inference(cnf_transformation,[],[f5])).
% 1.93/1.02  
% 1.93/1.02  fof(f11,conjecture,(
% 1.93/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f12,negated_conjecture,(
% 1.93/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 1.93/1.02    inference(negated_conjecture,[],[f11])).
% 1.93/1.02  
% 1.93/1.02  fof(f17,plain,(
% 1.93/1.02    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 1.93/1.02    inference(ennf_transformation,[],[f12])).
% 1.93/1.02  
% 1.93/1.02  fof(f19,plain,(
% 1.93/1.02    ( ! [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(X0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) & k2_struct_0(X0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.93/1.02    introduced(choice_axiom,[])).
% 1.93/1.02  
% 1.93/1.02  fof(f18,plain,(
% 1.93/1.02    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0)) => (? [X1] : (((k2_struct_0(sK0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) & k2_struct_0(sK0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0))),
% 1.93/1.02    introduced(choice_axiom,[])).
% 1.93/1.02  
% 1.93/1.02  fof(f20,plain,(
% 1.93/1.02    (((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0)),
% 1.93/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 1.93/1.02  
% 1.93/1.02  fof(f32,plain,(
% 1.93/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.93/1.02    inference(cnf_transformation,[],[f20])).
% 1.93/1.02  
% 1.93/1.02  fof(f36,plain,(
% 1.93/1.02    k2_struct_0(sK0) = sK1 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 1.93/1.02    inference(cnf_transformation,[],[f20])).
% 1.93/1.02  
% 1.93/1.02  fof(f10,axiom,(
% 1.93/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 1.93/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/1.02  
% 1.93/1.02  fof(f16,plain,(
% 1.93/1.02    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.93/1.02    inference(ennf_transformation,[],[f10])).
% 1.93/1.02  
% 1.93/1.02  fof(f30,plain,(
% 1.93/1.02    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.93/1.02    inference(cnf_transformation,[],[f16])).
% 1.93/1.02  
% 1.93/1.02  fof(f31,plain,(
% 1.93/1.02    l1_struct_0(sK0)),
% 1.93/1.02    inference(cnf_transformation,[],[f20])).
% 1.93/1.02  
% 1.93/1.02  fof(f33,plain,(
% 1.93/1.02    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1),
% 1.93/1.02    inference(cnf_transformation,[],[f20])).
% 1.93/1.02  
% 1.93/1.02  cnf(c_114,plain,
% 1.93/1.02      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | X1 != X0 ),
% 1.93/1.02      theory(equality) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_107,plain,
% 1.93/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 1.93/1.02      theory(equality) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_328,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1,plain,
% 1.93/1.02      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.93/1.02      inference(cnf_transformation,[],[f39]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_0,plain,
% 1.93/1.02      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 1.93/1.02      inference(cnf_transformation,[],[f38]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_6,plain,
% 1.93/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.93/1.02      inference(cnf_transformation,[],[f29]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_122,plain,
% 1.93/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.93/1.02      | X1 != X2
% 1.93/1.02      | k1_setfam_1(k2_tarski(X2,X3)) != X0 ),
% 1.93/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_123,plain,
% 1.93/1.02      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) ),
% 1.93/1.02      inference(unflattening,[status(thm)],[c_122]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_512,plain,
% 1.93/1.02      ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) = iProver_top ),
% 1.93/1.02      inference(predicate_to_equality,[status(thm)],[c_123]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_873,plain,
% 1.93/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_1,c_512]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_5,plain,
% 1.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.93/1.02      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 1.93/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_514,plain,
% 1.93/1.02      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 1.93/1.02      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 1.93/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1136,plain,
% 1.93/1.02      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = k7_subset_1(X1,k1_xboole_0,X0) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_873,c_514]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1445,plain,
% 1.93/1.02      ( k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(X2,k1_xboole_0,X1) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_1136,c_1136]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1134,plain,
% 1.93/1.02      ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2))) = k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_512,c_514]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1327,plain,
% 1.93/1.02      ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),k1_xboole_0) = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_xboole_0) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_1,c_1134]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_2,plain,
% 1.93/1.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.93/1.02      inference(cnf_transformation,[],[f24]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1335,plain,
% 1.93/1.02      ( k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),k1_xboole_0) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 1.93/1.02      inference(demodulation,[status(thm)],[c_1327,c_2]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1340,plain,
% 1.93/1.02      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_1,c_1335]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1341,plain,
% 1.93/1.02      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.93/1.02      inference(light_normalisation,[status(thm)],[c_1340,c_1]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_4,plain,
% 1.93/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.93/1.02      inference(cnf_transformation,[],[f26]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_515,plain,
% 1.93/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.93/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_3,plain,
% 1.93/1.02      ( k2_subset_1(X0) = X0 ),
% 1.93/1.02      inference(cnf_transformation,[],[f25]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_524,plain,
% 1.93/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.93/1.02      inference(light_normalisation,[status(thm)],[c_515,c_3]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1135,plain,
% 1.93/1.02      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_524,c_514]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1329,plain,
% 1.93/1.02      ( k7_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1)),X2) = k7_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)),X2) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_1134,c_1135]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_12,negated_conjecture,
% 1.93/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.93/1.02      inference(cnf_transformation,[],[f32]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_513,plain,
% 1.93/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.93/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1133,plain,
% 1.93/1.02      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_513,c_514]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1161,plain,
% 1.93/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 1.93/1.02      inference(demodulation,[status(thm)],[c_1133,c_1135]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1153,plain,
% 1.93/1.02      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_1,c_1135]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1155,plain,
% 1.93/1.02      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 1.93/1.02      inference(light_normalisation,[status(thm)],[c_1153,c_2]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1140,plain,
% 1.93/1.02      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 1.93/1.02      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 1.93/1.02      inference(demodulation,[status(thm)],[c_1135,c_514]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_8,negated_conjecture,
% 1.93/1.02      ( k2_struct_0(sK0) = sK1
% 1.93/1.02      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 1.93/1.02      inference(cnf_transformation,[],[f36]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_7,plain,
% 1.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.02      | ~ l1_struct_0(X1)
% 1.93/1.02      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 1.93/1.02      inference(cnf_transformation,[],[f30]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_13,negated_conjecture,
% 1.93/1.02      ( l1_struct_0(sK0) ),
% 1.93/1.02      inference(cnf_transformation,[],[f31]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_133,plain,
% 1.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/1.02      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
% 1.93/1.02      | sK0 != X1 ),
% 1.93/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_134,plain,
% 1.93/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.93/1.02      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
% 1.93/1.02      inference(unflattening,[status(thm)],[c_133]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_511,plain,
% 1.93/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 1.93/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.93/1.02      inference(predicate_to_equality,[status(thm)],[c_134]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_604,plain,
% 1.93/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_513,c_511]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_691,plain,
% 1.93/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
% 1.93/1.02      | k2_struct_0(sK0) = sK1 ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_8,c_604]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_957,plain,
% 1.93/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_873,c_511]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_1027,plain,
% 1.93/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
% 1.93/1.02      | k2_struct_0(sK0) = sK1 ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_691,c_957]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_954,plain,
% 1.93/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_524,c_511]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_742,plain,
% 1.93/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)) ),
% 1.93/1.02      inference(superposition,[status(thm)],[c_512,c_511]) ).
% 1.93/1.02  
% 1.93/1.02  cnf(c_11,negated_conjecture,
% 1.93/1.02      ( k2_struct_0(sK0) != sK1
% 1.93/1.02      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 1.93/1.02      inference(cnf_transformation,[],[f33]) ).
% 1.93/1.02  
% 1.93/1.02  
% 1.93/1.02  % SZS output end Saturation for theBenchmark.p
% 1.93/1.02  
% 1.93/1.02  ------                               Statistics
% 1.93/1.02  
% 1.93/1.02  ------ General
% 1.93/1.02  
% 1.93/1.02  abstr_ref_over_cycles:                  0
% 1.93/1.02  abstr_ref_under_cycles:                 0
% 1.93/1.02  gc_basic_clause_elim:                   0
% 1.93/1.02  forced_gc_time:                         0
% 1.93/1.02  parsing_time:                           0.01
% 1.93/1.02  unif_index_cands_time:                  0.
% 1.93/1.02  unif_index_add_time:                    0.
% 1.93/1.02  orderings_time:                         0.
% 1.93/1.02  out_proof_time:                         0.
% 1.93/1.02  total_time:                             0.106
% 1.93/1.02  num_of_symbols:                         45
% 1.93/1.02  num_of_terms:                           1652
% 1.93/1.02  
% 1.93/1.02  ------ Preprocessing
% 1.93/1.02  
% 1.93/1.02  num_of_splits:                          0
% 1.93/1.02  num_of_split_atoms:                     0
% 1.93/1.02  num_of_reused_defs:                     0
% 1.93/1.02  num_eq_ax_congr_red:                    10
% 1.93/1.02  num_of_sem_filtered_clauses:            1
% 1.93/1.02  num_of_subtypes:                        0
% 1.93/1.02  monotx_restored_types:                  0
% 1.93/1.02  sat_num_of_epr_types:                   0
% 1.93/1.02  sat_num_of_non_cyclic_types:            0
% 1.93/1.02  sat_guarded_non_collapsed_types:        0
% 1.93/1.02  num_pure_diseq_elim:                    0
% 1.93/1.02  simp_replaced_by:                       0
% 1.93/1.02  res_preprocessed:                       63
% 1.93/1.02  prep_upred:                             0
% 1.93/1.02  prep_unflattend:                        15
% 1.93/1.02  smt_new_axioms:                         0
% 1.93/1.02  pred_elim_cands:                        1
% 1.93/1.02  pred_elim:                              2
% 1.93/1.02  pred_elim_cl:                           2
% 1.93/1.02  pred_elim_cycles:                       4
% 1.93/1.02  merged_defs:                            8
% 1.93/1.02  merged_defs_ncl:                        0
% 1.93/1.02  bin_hyper_res:                          8
% 1.93/1.02  prep_cycles:                            4
% 1.93/1.02  pred_elim_time:                         0.003
% 1.93/1.02  splitting_time:                         0.
% 1.93/1.02  sem_filter_time:                        0.
% 1.93/1.02  monotx_time:                            0.
% 1.93/1.02  subtype_inf_time:                       0.
% 1.93/1.02  
% 1.93/1.02  ------ Problem properties
% 1.93/1.02  
% 1.93/1.02  clauses:                                10
% 1.93/1.02  conjectures:                            3
% 1.93/1.02  epr:                                    0
% 1.93/1.02  horn:                                   9
% 1.93/1.02  ground:                                 3
% 1.93/1.02  unary:                                  6
% 1.93/1.02  binary:                                 4
% 1.93/1.02  lits:                                   14
% 1.93/1.02  lits_eq:                                9
% 1.93/1.02  fd_pure:                                0
% 1.93/1.02  fd_pseudo:                              0
% 1.93/1.02  fd_cond:                                0
% 1.93/1.02  fd_pseudo_cond:                         0
% 1.93/1.02  ac_symbols:                             0
% 1.93/1.02  
% 1.93/1.02  ------ Propositional Solver
% 1.93/1.02  
% 1.93/1.02  prop_solver_calls:                      28
% 1.93/1.02  prop_fast_solver_calls:                 277
% 1.93/1.02  smt_solver_calls:                       0
% 1.93/1.02  smt_fast_solver_calls:                  0
% 1.93/1.02  prop_num_of_clauses:                    565
% 1.93/1.02  prop_preprocess_simplified:             2018
% 1.93/1.02  prop_fo_subsumed:                       0
% 1.93/1.02  prop_solver_time:                       0.
% 1.93/1.02  smt_solver_time:                        0.
% 1.93/1.02  smt_fast_solver_time:                   0.
% 1.93/1.02  prop_fast_solver_time:                  0.
% 1.93/1.02  prop_unsat_core_time:                   0.
% 1.93/1.02  
% 1.93/1.02  ------ QBF
% 1.93/1.02  
% 1.93/1.02  qbf_q_res:                              0
% 1.93/1.02  qbf_num_tautologies:                    0
% 1.93/1.02  qbf_prep_cycles:                        0
% 1.93/1.02  
% 1.93/1.02  ------ BMC1
% 1.93/1.02  
% 1.93/1.02  bmc1_current_bound:                     -1
% 1.93/1.02  bmc1_last_solved_bound:                 -1
% 1.93/1.02  bmc1_unsat_core_size:                   -1
% 1.93/1.02  bmc1_unsat_core_parents_size:           -1
% 1.93/1.02  bmc1_merge_next_fun:                    0
% 1.93/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.93/1.02  
% 1.93/1.02  ------ Instantiation
% 1.93/1.02  
% 1.93/1.02  inst_num_of_clauses:                    214
% 1.93/1.02  inst_num_in_passive:                    71
% 1.93/1.02  inst_num_in_active:                     132
% 1.93/1.02  inst_num_in_unprocessed:                11
% 1.93/1.02  inst_num_of_loops:                      140
% 1.93/1.02  inst_num_of_learning_restarts:          0
% 1.93/1.02  inst_num_moves_active_passive:          5
% 1.93/1.02  inst_lit_activity:                      0
% 1.93/1.02  inst_lit_activity_moves:                0
% 1.93/1.02  inst_num_tautologies:                   0
% 1.93/1.02  inst_num_prop_implied:                  0
% 1.93/1.02  inst_num_existing_simplified:           0
% 1.93/1.02  inst_num_eq_res_simplified:             0
% 1.93/1.02  inst_num_child_elim:                    0
% 1.93/1.02  inst_num_of_dismatching_blockings:      107
% 1.93/1.02  inst_num_of_non_proper_insts:           187
% 1.93/1.02  inst_num_of_duplicates:                 0
% 1.93/1.02  inst_inst_num_from_inst_to_res:         0
% 1.93/1.02  inst_dismatching_checking_time:         0.
% 1.93/1.02  
% 1.93/1.02  ------ Resolution
% 1.93/1.02  
% 1.93/1.02  res_num_of_clauses:                     0
% 1.93/1.02  res_num_in_passive:                     0
% 1.93/1.02  res_num_in_active:                      0
% 1.93/1.02  res_num_of_loops:                       67
% 1.93/1.02  res_forward_subset_subsumed:            16
% 1.93/1.02  res_backward_subset_subsumed:           0
% 1.93/1.02  res_forward_subsumed:                   0
% 1.93/1.02  res_backward_subsumed:                  0
% 1.93/1.02  res_forward_subsumption_resolution:     0
% 1.93/1.02  res_backward_subsumption_resolution:    0
% 1.93/1.02  res_clause_to_clause_subsumption:       57
% 1.93/1.02  res_orphan_elimination:                 0
% 1.93/1.02  res_tautology_del:                      28
% 1.93/1.02  res_num_eq_res_simplified:              0
% 1.93/1.02  res_num_sel_changes:                    0
% 1.93/1.02  res_moves_from_active_to_pass:          0
% 1.93/1.02  
% 1.93/1.02  ------ Superposition
% 1.93/1.02  
% 1.93/1.02  sup_time_total:                         0.
% 1.93/1.02  sup_time_generating:                    0.
% 1.93/1.02  sup_time_sim_full:                      0.
% 1.93/1.02  sup_time_sim_immed:                     0.
% 1.93/1.02  
% 1.93/1.02  sup_num_of_clauses:                     27
% 1.93/1.02  sup_num_in_active:                      26
% 1.93/1.02  sup_num_in_passive:                     1
% 1.93/1.02  sup_num_of_loops:                       27
% 1.93/1.02  sup_fw_superposition:                   35
% 1.93/1.02  sup_bw_superposition:                   22
% 1.93/1.02  sup_immediate_simplified:               10
% 1.93/1.02  sup_given_eliminated:                   1
% 1.93/1.02  comparisons_done:                       0
% 1.93/1.02  comparisons_avoided:                    3
% 1.93/1.02  
% 1.93/1.02  ------ Simplifications
% 1.93/1.02  
% 1.93/1.02  
% 1.93/1.02  sim_fw_subset_subsumed:                 0
% 1.93/1.02  sim_bw_subset_subsumed:                 0
% 1.93/1.02  sim_fw_subsumed:                        3
% 1.93/1.02  sim_bw_subsumed:                        0
% 1.93/1.02  sim_fw_subsumption_res:                 0
% 1.93/1.02  sim_bw_subsumption_res:                 0
% 1.93/1.02  sim_tautology_del:                      1
% 1.93/1.02  sim_eq_tautology_del:                   2
% 1.93/1.02  sim_eq_res_simp:                        0
% 1.93/1.02  sim_fw_demodulated:                     3
% 1.93/1.02  sim_bw_demodulated:                     1
% 1.93/1.02  sim_light_normalised:                   7
% 1.93/1.02  sim_joinable_taut:                      0
% 1.93/1.02  sim_joinable_simp:                      0
% 1.93/1.02  sim_ac_normalised:                      0
% 1.93/1.02  sim_smt_subsumption:                    0
% 1.93/1.02  
%------------------------------------------------------------------------------
