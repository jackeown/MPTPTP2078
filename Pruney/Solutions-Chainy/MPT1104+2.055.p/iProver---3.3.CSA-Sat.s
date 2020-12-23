%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:15 EST 2020

% Result     : CounterSatisfiable 2.89s
% Output     : Saturation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  169 (2975 expanded)
%              Number of clauses        :  121 ( 825 expanded)
%              Number of leaves         :   17 ( 803 expanded)
%              Depth                    :   17
%              Number of atoms          :  245 (6557 expanded)
%              Number of equality atoms :  182 (3708 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2
        & r1_xboole_0(X1,sK2)
        & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
            & r1_xboole_0(X1,X2)
            & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ? [X2] :
          ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2
          & r1_xboole_0(sK1,X2)
          & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f27,f36,f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f28,f42,f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,X1)),X0))) = k3_tarski(k2_tarski(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0))),X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f42,f31,f31,f42])).

fof(f40,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_85,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_150,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_263,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_272,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_263,c_5])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_262,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4462,plain,
    ( k4_subset_1(X0,X1,X0) = k3_tarski(k2_tarski(X1,X0))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_272,c_262])).

cnf(c_7775,plain,
    ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_272,c_4462])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_259,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7774,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_259,c_4462])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_260,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7773,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_260,c_4462])).

cnf(c_4,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_680,plain,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_261,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_689,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_272,c_261])).

cnf(c_1171,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_689])).

cnf(c_2422,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_680,c_1171])).

cnf(c_2420,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1,c_1171])).

cnf(c_3895,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_4,c_2420])).

cnf(c_7571,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_2422,c_3895])).

cnf(c_7569,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_4,c_2422])).

cnf(c_7559,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_3895,c_2422])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_577,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_881,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_577,c_1])).

cnf(c_1332,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_881,c_689])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_283,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_1])).

cnf(c_1340,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1332,c_283])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,X1)),X0))) = k3_tarski(k2_tarski(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0))),X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_99,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))),X1))
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_100,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,sK2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,sK2)),sK1))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))),sK2)) ),
    inference(unflattening,[status(thm)],[c_99])).

cnf(c_575,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,sK2)),k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(X0,sK2))))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))),sK2)) ),
    inference(demodulation,[status(thm)],[c_4,c_100])).

cnf(c_962,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),sK2)) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_577,c_575])).

cnf(c_566,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(superposition,[status(thm)],[c_260,c_261])).

cnf(c_887,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(X0,sK2))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(superposition,[status(thm)],[c_4,c_566])).

cnf(c_1066,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),sK2)) = k7_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_962,c_887])).

cnf(c_1068,plain,
    ( k3_tarski(k2_tarski(sK2,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,sK1))))) = k7_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(superposition,[status(thm)],[c_4,c_1066])).

cnf(c_1141,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_689,c_566])).

cnf(c_2539,plain,
    ( k3_tarski(k2_tarski(sK2,k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))) = k7_subset_1(sK2,sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_1068,c_689,c_1141])).

cnf(c_7092,plain,
    ( k7_subset_1(sK2,sK2,sK1) = k3_tarski(k2_tarski(sK2,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_1340,c_2539])).

cnf(c_7094,plain,
    ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_7092,c_0])).

cnf(c_4460,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_260,c_262])).

cnf(c_4551,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_259,c_4460])).

cnf(c_11,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4556,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4551,c_11])).

cnf(c_4728,plain,
    ( k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) = sK2 ),
    inference(superposition,[status(thm)],[c_4556,c_680])).

cnf(c_5120,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = k5_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_4728,c_1171])).

cnf(c_4715,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) ),
    inference(superposition,[status(thm)],[c_4556,c_3895])).

cnf(c_6763,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = k5_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(demodulation,[status(thm)],[c_5120,c_4715])).

cnf(c_4461,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,sK1) = k3_tarski(k2_tarski(X0,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_259,c_262])).

cnf(c_6192,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_272,c_4461])).

cnf(c_6191,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_259,c_4461])).

cnf(c_6190,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_260,c_4461])).

cnf(c_1140,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,sK2)),k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(X0,sK2))))) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_689,c_575])).

cnf(c_2427,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_1171,c_1140])).

cnf(c_4720,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(sK1,sK1,sK1),sK2)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_4556,c_2427])).

cnf(c_567,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_259,c_261])).

cnf(c_947,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k3_tarski(k2_tarski(sK1,X0))) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1,c_567])).

cnf(c_953,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k3_tarski(k2_tarski(sK1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_947,c_283])).

cnf(c_1142,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_689,c_567])).

cnf(c_2931,plain,
    ( k7_subset_1(sK1,sK1,k3_tarski(k2_tarski(sK1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_953,c_1142])).

cnf(c_2939,plain,
    ( k7_subset_1(sK1,sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2931])).

cnf(c_4744,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k3_tarski(k2_tarski(k1_xboole_0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4720,c_2939])).

cnf(c_4745,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_4744,c_577])).

cnf(c_4727,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4556,c_953])).

cnf(c_4726,plain,
    ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4556,c_2931])).

cnf(c_886,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_tarski(k2_tarski(sK2,X0))) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1,c_566])).

cnf(c_892,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_tarski(k2_tarski(sK2,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_886,c_283])).

cnf(c_2054,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_tarski(k2_tarski(X0,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_892])).

cnf(c_4723,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4556,c_2054])).

cnf(c_2069,plain,
    ( k7_subset_1(sK2,sK2,k3_tarski(k2_tarski(X0,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2054,c_1141])).

cnf(c_4722,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4556,c_2069])).

cnf(c_4719,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_4556,c_1])).

cnf(c_961,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))),sK2)) = k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_1,c_575])).

cnf(c_970,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK1),sK2)) = k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
    inference(demodulation,[status(thm)],[c_961,c_567])).

cnf(c_1055,plain,
    ( k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK1))) = k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_4,c_970])).

cnf(c_2439,plain,
    ( k3_tarski(k2_tarski(sK2,k7_subset_1(sK1,sK1,sK1))) = k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
    inference(demodulation,[status(thm)],[c_1055,c_1142])).

cnf(c_3286,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_2939,c_2439])).

cnf(c_3291,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_3286,c_0])).

cnf(c_4714,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_4556,c_3291])).

cnf(c_4552,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_272,c_4460])).

cnf(c_4550,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_260,c_4460])).

cnf(c_963,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,X0)),k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK2,X0))))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))),sK2)) ),
    inference(superposition,[status(thm)],[c_4,c_575])).

cnf(c_1139,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,X0)),k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK2,X0))))) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_689,c_963])).

cnf(c_3648,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(sK1,sK1,sK1),sK2)) = k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_680,c_1139])).

cnf(c_3655,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = k3_tarski(k2_tarski(k1_xboole_0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3648,c_2939])).

cnf(c_3656,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_3655,c_577])).

cnf(c_3637,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK2,X0)),sK1) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_4,c_2427])).

cnf(c_2940,plain,
    ( k7_subset_1(sK1,sK1,k3_tarski(k2_tarski(X0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_2931])).

cnf(c_2929,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k3_tarski(k2_tarski(X0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_953])).

cnf(c_2056,plain,
    ( k7_subset_1(sK2,sK2,k3_tarski(k2_tarski(sK2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_892,c_1141])).

cnf(c_2769,plain,
    ( k7_subset_1(sK2,sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2056])).

cnf(c_1334,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_881,c_887])).

cnf(c_1960,plain,
    ( k7_subset_1(sK2,sK2,k1_xboole_0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1141,c_1334])).

cnf(c_948,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_567])).

cnf(c_1333,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_881,c_948])).

cnf(c_1820,plain,
    ( k7_subset_1(sK1,sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1142,c_1333])).

cnf(c_1406,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_680,c_689])).

cnf(c_1408,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1406,c_283])).

cnf(c_1330,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_881])).

cnf(c_1396,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1330,c_689])).

cnf(c_679,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_1316,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_679,c_689])).

cnf(c_1326,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1316,c_283])).

cnf(c_1317,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_679,c_948])).

cnf(c_1323,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1317,c_283])).

cnf(c_1318,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_679,c_887])).

cnf(c_1320,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1318,c_283])).

cnf(c_1170,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_689])).

cnf(c_1182,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1170,c_283])).

cnf(c_1138,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_689,c_261])).

cnf(c_9,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n020.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 14:49:37 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running in FOF mode
% 2.89/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/0.96  
% 2.89/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/0.96  
% 2.89/0.96  ------  iProver source info
% 2.89/0.96  
% 2.89/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.89/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/0.96  git: non_committed_changes: false
% 2.89/0.96  git: last_make_outside_of_git: false
% 2.89/0.96  
% 2.89/0.96  ------ 
% 2.89/0.96  
% 2.89/0.96  ------ Input Options
% 2.89/0.96  
% 2.89/0.96  --out_options                           all
% 2.89/0.96  --tptp_safe_out                         true
% 2.89/0.96  --problem_path                          ""
% 2.89/0.96  --include_path                          ""
% 2.89/0.96  --clausifier                            res/vclausify_rel
% 2.89/0.96  --clausifier_options                    --mode clausify
% 2.89/0.96  --stdin                                 false
% 2.89/0.96  --stats_out                             all
% 2.89/0.96  
% 2.89/0.96  ------ General Options
% 2.89/0.96  
% 2.89/0.96  --fof                                   false
% 2.89/0.96  --time_out_real                         305.
% 2.89/0.96  --time_out_virtual                      -1.
% 2.89/0.96  --symbol_type_check                     false
% 2.89/0.96  --clausify_out                          false
% 2.89/0.96  --sig_cnt_out                           false
% 2.89/0.96  --trig_cnt_out                          false
% 2.89/0.96  --trig_cnt_out_tolerance                1.
% 2.89/0.96  --trig_cnt_out_sk_spl                   false
% 2.89/0.96  --abstr_cl_out                          false
% 2.89/0.96  
% 2.89/0.96  ------ Global Options
% 2.89/0.96  
% 2.89/0.96  --schedule                              default
% 2.89/0.96  --add_important_lit                     false
% 2.89/0.96  --prop_solver_per_cl                    1000
% 2.89/0.96  --min_unsat_core                        false
% 2.89/0.96  --soft_assumptions                      false
% 2.89/0.96  --soft_lemma_size                       3
% 2.89/0.96  --prop_impl_unit_size                   0
% 2.89/0.96  --prop_impl_unit                        []
% 2.89/0.96  --share_sel_clauses                     true
% 2.89/0.96  --reset_solvers                         false
% 2.89/0.96  --bc_imp_inh                            [conj_cone]
% 2.89/0.96  --conj_cone_tolerance                   3.
% 2.89/0.96  --extra_neg_conj                        none
% 2.89/0.96  --large_theory_mode                     true
% 2.89/0.96  --prolific_symb_bound                   200
% 2.89/0.96  --lt_threshold                          2000
% 2.89/0.96  --clause_weak_htbl                      true
% 2.89/0.96  --gc_record_bc_elim                     false
% 2.89/0.96  
% 2.89/0.96  ------ Preprocessing Options
% 2.89/0.96  
% 2.89/0.96  --preprocessing_flag                    true
% 2.89/0.96  --time_out_prep_mult                    0.1
% 2.89/0.96  --splitting_mode                        input
% 2.89/0.96  --splitting_grd                         true
% 2.89/0.96  --splitting_cvd                         false
% 2.89/0.96  --splitting_cvd_svl                     false
% 2.89/0.96  --splitting_nvd                         32
% 2.89/0.96  --sub_typing                            true
% 2.89/0.96  --prep_gs_sim                           true
% 2.89/0.96  --prep_unflatten                        true
% 2.89/0.96  --prep_res_sim                          true
% 2.89/0.96  --prep_upred                            true
% 2.89/0.96  --prep_sem_filter                       exhaustive
% 2.89/0.96  --prep_sem_filter_out                   false
% 2.89/0.96  --pred_elim                             true
% 2.89/0.96  --res_sim_input                         true
% 2.89/0.96  --eq_ax_congr_red                       true
% 2.89/0.96  --pure_diseq_elim                       true
% 2.89/0.96  --brand_transform                       false
% 2.89/0.96  --non_eq_to_eq                          false
% 2.89/0.96  --prep_def_merge                        true
% 2.89/0.96  --prep_def_merge_prop_impl              false
% 2.89/0.96  --prep_def_merge_mbd                    true
% 2.89/0.96  --prep_def_merge_tr_red                 false
% 2.89/0.96  --prep_def_merge_tr_cl                  false
% 2.89/0.96  --smt_preprocessing                     true
% 2.89/0.96  --smt_ac_axioms                         fast
% 2.89/0.96  --preprocessed_out                      false
% 2.89/0.96  --preprocessed_stats                    false
% 2.89/0.96  
% 2.89/0.96  ------ Abstraction refinement Options
% 2.89/0.96  
% 2.89/0.96  --abstr_ref                             []
% 2.89/0.96  --abstr_ref_prep                        false
% 2.89/0.96  --abstr_ref_until_sat                   false
% 2.89/0.96  --abstr_ref_sig_restrict                funpre
% 2.89/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.96  --abstr_ref_under                       []
% 2.89/0.96  
% 2.89/0.96  ------ SAT Options
% 2.89/0.96  
% 2.89/0.96  --sat_mode                              false
% 2.89/0.96  --sat_fm_restart_options                ""
% 2.89/0.96  --sat_gr_def                            false
% 2.89/0.96  --sat_epr_types                         true
% 2.89/0.96  --sat_non_cyclic_types                  false
% 2.89/0.96  --sat_finite_models                     false
% 2.89/0.96  --sat_fm_lemmas                         false
% 2.89/0.96  --sat_fm_prep                           false
% 2.89/0.96  --sat_fm_uc_incr                        true
% 2.89/0.96  --sat_out_model                         small
% 2.89/0.96  --sat_out_clauses                       false
% 2.89/0.96  
% 2.89/0.96  ------ QBF Options
% 2.89/0.96  
% 2.89/0.96  --qbf_mode                              false
% 2.89/0.96  --qbf_elim_univ                         false
% 2.89/0.96  --qbf_dom_inst                          none
% 2.89/0.96  --qbf_dom_pre_inst                      false
% 2.89/0.96  --qbf_sk_in                             false
% 2.89/0.96  --qbf_pred_elim                         true
% 2.89/0.96  --qbf_split                             512
% 2.89/0.96  
% 2.89/0.96  ------ BMC1 Options
% 2.89/0.96  
% 2.89/0.96  --bmc1_incremental                      false
% 2.89/0.96  --bmc1_axioms                           reachable_all
% 2.89/0.96  --bmc1_min_bound                        0
% 2.89/0.96  --bmc1_max_bound                        -1
% 2.89/0.96  --bmc1_max_bound_default                -1
% 2.89/0.96  --bmc1_symbol_reachability              true
% 2.89/0.96  --bmc1_property_lemmas                  false
% 2.89/0.96  --bmc1_k_induction                      false
% 2.89/0.96  --bmc1_non_equiv_states                 false
% 2.89/0.96  --bmc1_deadlock                         false
% 2.89/0.96  --bmc1_ucm                              false
% 2.89/0.96  --bmc1_add_unsat_core                   none
% 2.89/0.96  --bmc1_unsat_core_children              false
% 2.89/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.96  --bmc1_out_stat                         full
% 2.89/0.96  --bmc1_ground_init                      false
% 2.89/0.96  --bmc1_pre_inst_next_state              false
% 2.89/0.96  --bmc1_pre_inst_state                   false
% 2.89/0.96  --bmc1_pre_inst_reach_state             false
% 2.89/0.96  --bmc1_out_unsat_core                   false
% 2.89/0.96  --bmc1_aig_witness_out                  false
% 2.89/0.96  --bmc1_verbose                          false
% 2.89/0.96  --bmc1_dump_clauses_tptp                false
% 2.89/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.96  --bmc1_dump_file                        -
% 2.89/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.96  --bmc1_ucm_extend_mode                  1
% 2.89/0.96  --bmc1_ucm_init_mode                    2
% 2.89/0.96  --bmc1_ucm_cone_mode                    none
% 2.89/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.96  --bmc1_ucm_relax_model                  4
% 2.89/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.96  --bmc1_ucm_layered_model                none
% 2.89/0.96  --bmc1_ucm_max_lemma_size               10
% 2.89/0.96  
% 2.89/0.96  ------ AIG Options
% 2.89/0.96  
% 2.89/0.96  --aig_mode                              false
% 2.89/0.96  
% 2.89/0.96  ------ Instantiation Options
% 2.89/0.96  
% 2.89/0.96  --instantiation_flag                    true
% 2.89/0.96  --inst_sos_flag                         false
% 2.89/0.96  --inst_sos_phase                        true
% 2.89/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.96  --inst_lit_sel_side                     num_symb
% 2.89/0.96  --inst_solver_per_active                1400
% 2.89/0.96  --inst_solver_calls_frac                1.
% 2.89/0.96  --inst_passive_queue_type               priority_queues
% 2.89/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.96  --inst_passive_queues_freq              [25;2]
% 2.89/0.96  --inst_dismatching                      true
% 2.89/0.96  --inst_eager_unprocessed_to_passive     true
% 2.89/0.96  --inst_prop_sim_given                   true
% 2.89/0.96  --inst_prop_sim_new                     false
% 2.89/0.96  --inst_subs_new                         false
% 2.89/0.96  --inst_eq_res_simp                      false
% 2.89/0.96  --inst_subs_given                       false
% 2.89/0.96  --inst_orphan_elimination               true
% 2.89/0.96  --inst_learning_loop_flag               true
% 2.89/0.96  --inst_learning_start                   3000
% 2.89/0.96  --inst_learning_factor                  2
% 2.89/0.96  --inst_start_prop_sim_after_learn       3
% 2.89/0.96  --inst_sel_renew                        solver
% 2.89/0.96  --inst_lit_activity_flag                true
% 2.89/0.96  --inst_restr_to_given                   false
% 2.89/0.96  --inst_activity_threshold               500
% 2.89/0.96  --inst_out_proof                        true
% 2.89/0.96  
% 2.89/0.96  ------ Resolution Options
% 2.89/0.96  
% 2.89/0.96  --resolution_flag                       true
% 2.89/0.96  --res_lit_sel                           adaptive
% 2.89/0.96  --res_lit_sel_side                      none
% 2.89/0.96  --res_ordering                          kbo
% 2.89/0.96  --res_to_prop_solver                    active
% 2.89/0.96  --res_prop_simpl_new                    false
% 2.89/0.96  --res_prop_simpl_given                  true
% 2.89/0.96  --res_passive_queue_type                priority_queues
% 2.89/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.96  --res_passive_queues_freq               [15;5]
% 2.89/0.96  --res_forward_subs                      full
% 2.89/0.96  --res_backward_subs                     full
% 2.89/0.96  --res_forward_subs_resolution           true
% 2.89/0.96  --res_backward_subs_resolution          true
% 2.89/0.96  --res_orphan_elimination                true
% 2.89/0.96  --res_time_limit                        2.
% 2.89/0.96  --res_out_proof                         true
% 2.89/0.96  
% 2.89/0.96  ------ Superposition Options
% 2.89/0.96  
% 2.89/0.96  --superposition_flag                    true
% 2.89/0.96  --sup_passive_queue_type                priority_queues
% 2.89/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.96  --demod_completeness_check              fast
% 2.89/0.96  --demod_use_ground                      true
% 2.89/0.96  --sup_to_prop_solver                    passive
% 2.89/0.96  --sup_prop_simpl_new                    true
% 2.89/0.96  --sup_prop_simpl_given                  true
% 2.89/0.96  --sup_fun_splitting                     false
% 2.89/0.96  --sup_smt_interval                      50000
% 2.89/0.96  
% 2.89/0.96  ------ Superposition Simplification Setup
% 2.89/0.96  
% 2.89/0.96  --sup_indices_passive                   []
% 2.89/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.96  --sup_full_bw                           [BwDemod]
% 2.89/0.96  --sup_immed_triv                        [TrivRules]
% 2.89/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.96  --sup_immed_bw_main                     []
% 2.89/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.96  
% 2.89/0.96  ------ Combination Options
% 2.89/0.96  
% 2.89/0.96  --comb_res_mult                         3
% 2.89/0.96  --comb_sup_mult                         2
% 2.89/0.96  --comb_inst_mult                        10
% 2.89/0.96  
% 2.89/0.96  ------ Debug Options
% 2.89/0.96  
% 2.89/0.96  --dbg_backtrace                         false
% 2.89/0.96  --dbg_dump_prop_clauses                 false
% 2.89/0.96  --dbg_dump_prop_clauses_file            -
% 2.89/0.96  --dbg_out_stat                          false
% 2.89/0.96  ------ Parsing...
% 2.89/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/0.96  
% 2.89/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.89/0.96  
% 2.89/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/0.96  
% 2.89/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/0.96  ------ Proving...
% 2.89/0.96  ------ Problem Properties 
% 2.89/0.96  
% 2.89/0.96  
% 2.89/0.96  clauses                                 13
% 2.89/0.96  conjectures                             4
% 2.89/0.96  EPR                                     0
% 2.89/0.96  Horn                                    13
% 2.89/0.96  unary                                   11
% 2.89/0.96  binary                                  1
% 2.89/0.96  lits                                    16
% 2.89/0.96  lits eq                                 10
% 2.89/0.96  fd_pure                                 0
% 2.89/0.96  fd_pseudo                               0
% 2.89/0.96  fd_cond                                 0
% 2.89/0.96  fd_pseudo_cond                          0
% 2.89/0.96  AC symbols                              0
% 2.89/0.96  
% 2.89/0.96  ------ Schedule dynamic 5 is on 
% 2.89/0.96  
% 2.89/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/0.96  
% 2.89/0.96  
% 2.89/0.96  ------ 
% 2.89/0.96  Current options:
% 2.89/0.96  ------ 
% 2.89/0.96  
% 2.89/0.96  ------ Input Options
% 2.89/0.96  
% 2.89/0.96  --out_options                           all
% 2.89/0.96  --tptp_safe_out                         true
% 2.89/0.96  --problem_path                          ""
% 2.89/0.96  --include_path                          ""
% 2.89/0.96  --clausifier                            res/vclausify_rel
% 2.89/0.96  --clausifier_options                    --mode clausify
% 2.89/0.96  --stdin                                 false
% 2.89/0.96  --stats_out                             all
% 2.89/0.96  
% 2.89/0.96  ------ General Options
% 2.89/0.96  
% 2.89/0.96  --fof                                   false
% 2.89/0.96  --time_out_real                         305.
% 2.89/0.96  --time_out_virtual                      -1.
% 2.89/0.96  --symbol_type_check                     false
% 2.89/0.96  --clausify_out                          false
% 2.89/0.96  --sig_cnt_out                           false
% 2.89/0.96  --trig_cnt_out                          false
% 2.89/0.96  --trig_cnt_out_tolerance                1.
% 2.89/0.96  --trig_cnt_out_sk_spl                   false
% 2.89/0.96  --abstr_cl_out                          false
% 2.89/0.96  
% 2.89/0.96  ------ Global Options
% 2.89/0.96  
% 2.89/0.96  --schedule                              default
% 2.89/0.96  --add_important_lit                     false
% 2.89/0.96  --prop_solver_per_cl                    1000
% 2.89/0.96  --min_unsat_core                        false
% 2.89/0.96  --soft_assumptions                      false
% 2.89/0.96  --soft_lemma_size                       3
% 2.89/0.96  --prop_impl_unit_size                   0
% 2.89/0.96  --prop_impl_unit                        []
% 2.89/0.96  --share_sel_clauses                     true
% 2.89/0.96  --reset_solvers                         false
% 2.89/0.96  --bc_imp_inh                            [conj_cone]
% 2.89/0.96  --conj_cone_tolerance                   3.
% 2.89/0.96  --extra_neg_conj                        none
% 2.89/0.96  --large_theory_mode                     true
% 2.89/0.96  --prolific_symb_bound                   200
% 2.89/0.96  --lt_threshold                          2000
% 2.89/0.96  --clause_weak_htbl                      true
% 2.89/0.96  --gc_record_bc_elim                     false
% 2.89/0.96  
% 2.89/0.96  ------ Preprocessing Options
% 2.89/0.96  
% 2.89/0.96  --preprocessing_flag                    true
% 2.89/0.96  --time_out_prep_mult                    0.1
% 2.89/0.96  --splitting_mode                        input
% 2.89/0.96  --splitting_grd                         true
% 2.89/0.96  --splitting_cvd                         false
% 2.89/0.96  --splitting_cvd_svl                     false
% 2.89/0.96  --splitting_nvd                         32
% 2.89/0.96  --sub_typing                            true
% 2.89/0.96  --prep_gs_sim                           true
% 2.89/0.96  --prep_unflatten                        true
% 2.89/0.96  --prep_res_sim                          true
% 2.89/0.96  --prep_upred                            true
% 2.89/0.96  --prep_sem_filter                       exhaustive
% 2.89/0.96  --prep_sem_filter_out                   false
% 2.89/0.96  --pred_elim                             true
% 2.89/0.96  --res_sim_input                         true
% 2.89/0.96  --eq_ax_congr_red                       true
% 2.89/0.96  --pure_diseq_elim                       true
% 2.89/0.96  --brand_transform                       false
% 2.89/0.96  --non_eq_to_eq                          false
% 2.89/0.96  --prep_def_merge                        true
% 2.89/0.96  --prep_def_merge_prop_impl              false
% 2.89/0.96  --prep_def_merge_mbd                    true
% 2.89/0.96  --prep_def_merge_tr_red                 false
% 2.89/0.96  --prep_def_merge_tr_cl                  false
% 2.89/0.96  --smt_preprocessing                     true
% 2.89/0.96  --smt_ac_axioms                         fast
% 2.89/0.96  --preprocessed_out                      false
% 2.89/0.96  --preprocessed_stats                    false
% 2.89/0.96  
% 2.89/0.96  ------ Abstraction refinement Options
% 2.89/0.96  
% 2.89/0.96  --abstr_ref                             []
% 2.89/0.96  --abstr_ref_prep                        false
% 2.89/0.96  --abstr_ref_until_sat                   false
% 2.89/0.96  --abstr_ref_sig_restrict                funpre
% 2.89/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/0.96  --abstr_ref_under                       []
% 2.89/0.96  
% 2.89/0.96  ------ SAT Options
% 2.89/0.96  
% 2.89/0.96  --sat_mode                              false
% 2.89/0.96  --sat_fm_restart_options                ""
% 2.89/0.96  --sat_gr_def                            false
% 2.89/0.96  --sat_epr_types                         true
% 2.89/0.96  --sat_non_cyclic_types                  false
% 2.89/0.96  --sat_finite_models                     false
% 2.89/0.96  --sat_fm_lemmas                         false
% 2.89/0.96  --sat_fm_prep                           false
% 2.89/0.96  --sat_fm_uc_incr                        true
% 2.89/0.96  --sat_out_model                         small
% 2.89/0.96  --sat_out_clauses                       false
% 2.89/0.96  
% 2.89/0.96  ------ QBF Options
% 2.89/0.96  
% 2.89/0.96  --qbf_mode                              false
% 2.89/0.96  --qbf_elim_univ                         false
% 2.89/0.96  --qbf_dom_inst                          none
% 2.89/0.96  --qbf_dom_pre_inst                      false
% 2.89/0.96  --qbf_sk_in                             false
% 2.89/0.96  --qbf_pred_elim                         true
% 2.89/0.96  --qbf_split                             512
% 2.89/0.96  
% 2.89/0.96  ------ BMC1 Options
% 2.89/0.96  
% 2.89/0.96  --bmc1_incremental                      false
% 2.89/0.96  --bmc1_axioms                           reachable_all
% 2.89/0.96  --bmc1_min_bound                        0
% 2.89/0.96  --bmc1_max_bound                        -1
% 2.89/0.96  --bmc1_max_bound_default                -1
% 2.89/0.96  --bmc1_symbol_reachability              true
% 2.89/0.96  --bmc1_property_lemmas                  false
% 2.89/0.96  --bmc1_k_induction                      false
% 2.89/0.96  --bmc1_non_equiv_states                 false
% 2.89/0.96  --bmc1_deadlock                         false
% 2.89/0.96  --bmc1_ucm                              false
% 2.89/0.96  --bmc1_add_unsat_core                   none
% 2.89/0.96  --bmc1_unsat_core_children              false
% 2.89/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/0.96  --bmc1_out_stat                         full
% 2.89/0.96  --bmc1_ground_init                      false
% 2.89/0.96  --bmc1_pre_inst_next_state              false
% 2.89/0.96  --bmc1_pre_inst_state                   false
% 2.89/0.96  --bmc1_pre_inst_reach_state             false
% 2.89/0.96  --bmc1_out_unsat_core                   false
% 2.89/0.96  --bmc1_aig_witness_out                  false
% 2.89/0.96  --bmc1_verbose                          false
% 2.89/0.96  --bmc1_dump_clauses_tptp                false
% 2.89/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.89/0.96  --bmc1_dump_file                        -
% 2.89/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.89/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.89/0.96  --bmc1_ucm_extend_mode                  1
% 2.89/0.96  --bmc1_ucm_init_mode                    2
% 2.89/0.96  --bmc1_ucm_cone_mode                    none
% 2.89/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.89/0.96  --bmc1_ucm_relax_model                  4
% 2.89/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.89/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/0.96  --bmc1_ucm_layered_model                none
% 2.89/0.96  --bmc1_ucm_max_lemma_size               10
% 2.89/0.96  
% 2.89/0.96  ------ AIG Options
% 2.89/0.96  
% 2.89/0.96  --aig_mode                              false
% 2.89/0.96  
% 2.89/0.96  ------ Instantiation Options
% 2.89/0.96  
% 2.89/0.96  --instantiation_flag                    true
% 2.89/0.96  --inst_sos_flag                         false
% 2.89/0.96  --inst_sos_phase                        true
% 2.89/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/0.96  --inst_lit_sel_side                     none
% 2.89/0.96  --inst_solver_per_active                1400
% 2.89/0.96  --inst_solver_calls_frac                1.
% 2.89/0.96  --inst_passive_queue_type               priority_queues
% 2.89/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/0.96  --inst_passive_queues_freq              [25;2]
% 2.89/0.96  --inst_dismatching                      true
% 2.89/0.96  --inst_eager_unprocessed_to_passive     true
% 2.89/0.96  --inst_prop_sim_given                   true
% 2.89/0.96  --inst_prop_sim_new                     false
% 2.89/0.96  --inst_subs_new                         false
% 2.89/0.96  --inst_eq_res_simp                      false
% 2.89/0.96  --inst_subs_given                       false
% 2.89/0.96  --inst_orphan_elimination               true
% 2.89/0.96  --inst_learning_loop_flag               true
% 2.89/0.96  --inst_learning_start                   3000
% 2.89/0.96  --inst_learning_factor                  2
% 2.89/0.96  --inst_start_prop_sim_after_learn       3
% 2.89/0.96  --inst_sel_renew                        solver
% 2.89/0.96  --inst_lit_activity_flag                true
% 2.89/0.96  --inst_restr_to_given                   false
% 2.89/0.96  --inst_activity_threshold               500
% 2.89/0.96  --inst_out_proof                        true
% 2.89/0.96  
% 2.89/0.96  ------ Resolution Options
% 2.89/0.96  
% 2.89/0.96  --resolution_flag                       false
% 2.89/0.96  --res_lit_sel                           adaptive
% 2.89/0.96  --res_lit_sel_side                      none
% 2.89/0.96  --res_ordering                          kbo
% 2.89/0.96  --res_to_prop_solver                    active
% 2.89/0.96  --res_prop_simpl_new                    false
% 2.89/0.96  --res_prop_simpl_given                  true
% 2.89/0.96  --res_passive_queue_type                priority_queues
% 2.89/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/0.96  --res_passive_queues_freq               [15;5]
% 2.89/0.96  --res_forward_subs                      full
% 2.89/0.96  --res_backward_subs                     full
% 2.89/0.96  --res_forward_subs_resolution           true
% 2.89/0.96  --res_backward_subs_resolution          true
% 2.89/0.96  --res_orphan_elimination                true
% 2.89/0.96  --res_time_limit                        2.
% 2.89/0.96  --res_out_proof                         true
% 2.89/0.96  
% 2.89/0.96  ------ Superposition Options
% 2.89/0.96  
% 2.89/0.96  --superposition_flag                    true
% 2.89/0.96  --sup_passive_queue_type                priority_queues
% 2.89/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.89/0.96  --demod_completeness_check              fast
% 2.89/0.96  --demod_use_ground                      true
% 2.89/0.96  --sup_to_prop_solver                    passive
% 2.89/0.96  --sup_prop_simpl_new                    true
% 2.89/0.96  --sup_prop_simpl_given                  true
% 2.89/0.96  --sup_fun_splitting                     false
% 2.89/0.96  --sup_smt_interval                      50000
% 2.89/0.96  
% 2.89/0.96  ------ Superposition Simplification Setup
% 2.89/0.96  
% 2.89/0.96  --sup_indices_passive                   []
% 2.89/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.96  --sup_full_bw                           [BwDemod]
% 2.89/0.96  --sup_immed_triv                        [TrivRules]
% 2.89/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.96  --sup_immed_bw_main                     []
% 2.89/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/0.96  
% 2.89/0.96  ------ Combination Options
% 2.89/0.96  
% 2.89/0.96  --comb_res_mult                         3
% 2.89/0.96  --comb_sup_mult                         2
% 2.89/0.96  --comb_inst_mult                        10
% 2.89/0.96  
% 2.89/0.96  ------ Debug Options
% 2.89/0.96  
% 2.89/0.96  --dbg_backtrace                         false
% 2.89/0.96  --dbg_dump_prop_clauses                 false
% 2.89/0.96  --dbg_dump_prop_clauses_file            -
% 2.89/0.96  --dbg_out_stat                          false
% 2.89/0.96  
% 2.89/0.96  
% 2.89/0.96  
% 2.89/0.96  
% 2.89/0.96  ------ Proving...
% 2.89/0.96  
% 2.89/0.96  
% 2.89/0.96  % SZS status CounterSatisfiable for theBenchmark.p
% 2.89/0.96  
% 2.89/0.96  % SZS output start Saturation for theBenchmark.p
% 2.89/0.96  
% 2.89/0.96  fof(f9,axiom,(
% 2.89/0.96    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f33,plain,(
% 2.89/0.96    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.89/0.96    inference(cnf_transformation,[],[f9])).
% 2.89/0.96  
% 2.89/0.96  fof(f8,axiom,(
% 2.89/0.96    ! [X0] : k2_subset_1(X0) = X0),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f32,plain,(
% 2.89/0.96    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.89/0.96    inference(cnf_transformation,[],[f8])).
% 2.89/0.96  
% 2.89/0.96  fof(f10,axiom,(
% 2.89/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f17,plain,(
% 2.89/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.89/0.96    inference(ennf_transformation,[],[f10])).
% 2.89/0.96  
% 2.89/0.96  fof(f18,plain,(
% 2.89/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.89/0.96    inference(flattening,[],[f17])).
% 2.89/0.96  
% 2.89/0.96  fof(f34,plain,(
% 2.89/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.89/0.96    inference(cnf_transformation,[],[f18])).
% 2.89/0.96  
% 2.89/0.96  fof(f7,axiom,(
% 2.89/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f31,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.89/0.96    inference(cnf_transformation,[],[f7])).
% 2.89/0.96  
% 2.89/0.96  fof(f47,plain,(
% 2.89/0.96    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.89/0.96    inference(definition_unfolding,[],[f34,f31])).
% 2.89/0.96  
% 2.89/0.96  fof(f13,conjecture,(
% 2.89/0.96    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f14,negated_conjecture,(
% 2.89/0.96    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 2.89/0.96    inference(negated_conjecture,[],[f13])).
% 2.89/0.96  
% 2.89/0.96  fof(f15,plain,(
% 2.89/0.96    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 2.89/0.96    inference(pure_predicate_removal,[],[f14])).
% 2.89/0.96  
% 2.89/0.96  fof(f20,plain,(
% 2.89/0.96    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 2.89/0.96    inference(ennf_transformation,[],[f15])).
% 2.89/0.96  
% 2.89/0.96  fof(f21,plain,(
% 2.89/0.96    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 2.89/0.96    inference(flattening,[],[f20])).
% 2.89/0.96  
% 2.89/0.96  fof(f23,plain,(
% 2.89/0.96    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.89/0.96    introduced(choice_axiom,[])).
% 2.89/0.96  
% 2.89/0.96  fof(f22,plain,(
% 2.89/0.96    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.89/0.96    introduced(choice_axiom,[])).
% 2.89/0.96  
% 2.89/0.96  fof(f24,plain,(
% 2.89/0.96    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.89/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 2.89/0.96  
% 2.89/0.96  fof(f37,plain,(
% 2.89/0.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.89/0.96    inference(cnf_transformation,[],[f24])).
% 2.89/0.96  
% 2.89/0.96  fof(f38,plain,(
% 2.89/0.96    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.89/0.96    inference(cnf_transformation,[],[f24])).
% 2.89/0.96  
% 2.89/0.96  fof(f6,axiom,(
% 2.89/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f30,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.89/0.96    inference(cnf_transformation,[],[f6])).
% 2.89/0.96  
% 2.89/0.96  fof(f3,axiom,(
% 2.89/0.96    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f27,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.89/0.96    inference(cnf_transformation,[],[f3])).
% 2.89/0.96  
% 2.89/0.96  fof(f12,axiom,(
% 2.89/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f36,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.89/0.96    inference(cnf_transformation,[],[f12])).
% 2.89/0.96  
% 2.89/0.96  fof(f44,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0) )),
% 2.89/0.96    inference(definition_unfolding,[],[f27,f36,f31])).
% 2.89/0.96  
% 2.89/0.96  fof(f11,axiom,(
% 2.89/0.96    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f19,plain,(
% 2.89/0.96    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.89/0.96    inference(ennf_transformation,[],[f11])).
% 2.89/0.96  
% 2.89/0.96  fof(f35,plain,(
% 2.89/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.89/0.96    inference(cnf_transformation,[],[f19])).
% 2.89/0.96  
% 2.89/0.96  fof(f1,axiom,(
% 2.89/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f25,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.89/0.96    inference(cnf_transformation,[],[f1])).
% 2.89/0.96  
% 2.89/0.96  fof(f42,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.89/0.96    inference(definition_unfolding,[],[f25,f36])).
% 2.89/0.96  
% 2.89/0.96  fof(f48,plain,(
% 2.89/0.96    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.89/0.96    inference(definition_unfolding,[],[f35,f42])).
% 2.89/0.96  
% 2.89/0.96  fof(f2,axiom,(
% 2.89/0.96    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f26,plain,(
% 2.89/0.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.89/0.96    inference(cnf_transformation,[],[f2])).
% 2.89/0.96  
% 2.89/0.96  fof(f43,plain,(
% 2.89/0.96    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 2.89/0.96    inference(definition_unfolding,[],[f26,f31])).
% 2.89/0.96  
% 2.89/0.96  fof(f4,axiom,(
% 2.89/0.96    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f28,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.89/0.96    inference(cnf_transformation,[],[f4])).
% 2.89/0.96  
% 2.89/0.96  fof(f45,plain,(
% 2.89/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0) )),
% 2.89/0.96    inference(definition_unfolding,[],[f28,f42,f31])).
% 2.89/0.96  
% 2.89/0.96  fof(f5,axiom,(
% 2.89/0.96    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1))),
% 2.89/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/0.96  
% 2.89/0.96  fof(f16,plain,(
% 2.89/0.96    ! [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) | ~r1_xboole_0(X0,X1))),
% 2.89/0.96    inference(ennf_transformation,[],[f5])).
% 2.89/0.96  
% 2.89/0.96  fof(f29,plain,(
% 2.89/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X2,X1),X0) = k2_xboole_0(k4_xboole_0(X2,X0),X1) | ~r1_xboole_0(X0,X1)) )),
% 2.89/0.96    inference(cnf_transformation,[],[f16])).
% 2.89/0.96  
% 2.89/0.96  fof(f46,plain,(
% 2.89/0.96    ( ! [X2,X0,X1] : (k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,X1)),X0))) = k3_tarski(k2_tarski(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0))),X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.89/0.96    inference(definition_unfolding,[],[f29,f42,f31,f31,f42])).
% 2.89/0.96  
% 2.89/0.96  fof(f40,plain,(
% 2.89/0.96    r1_xboole_0(sK1,sK2)),
% 2.89/0.96    inference(cnf_transformation,[],[f24])).
% 2.89/0.96  
% 2.89/0.96  fof(f39,plain,(
% 2.89/0.96    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 2.89/0.96    inference(cnf_transformation,[],[f24])).
% 2.89/0.96  
% 2.89/0.96  fof(f41,plain,(
% 2.89/0.96    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 2.89/0.96    inference(cnf_transformation,[],[f24])).
% 2.89/0.96  
% 2.89/0.96  cnf(c_85,plain,
% 2.89/0.96      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.89/0.96      theory(equality) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_150,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_6,plain,
% 2.89/0.96      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.89/0.96      inference(cnf_transformation,[],[f33]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_263,plain,
% 2.89/0.96      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.89/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_5,plain,
% 2.89/0.96      ( k2_subset_1(X0) = X0 ),
% 2.89/0.96      inference(cnf_transformation,[],[f32]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_272,plain,
% 2.89/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.89/0.96      inference(light_normalisation,[status(thm)],[c_263,c_5]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7,plain,
% 2.89/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.89/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.89/0.96      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 2.89/0.96      inference(cnf_transformation,[],[f47]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_262,plain,
% 2.89/0.96      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 2.89/0.96      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 2.89/0.96      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.89/0.96      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4462,plain,
% 2.89/0.96      ( k4_subset_1(X0,X1,X0) = k3_tarski(k2_tarski(X1,X0))
% 2.89/0.96      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_272,c_262]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7775,plain,
% 2.89/0.96      ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_272,c_4462]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_13,negated_conjecture,
% 2.89/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.89/0.96      inference(cnf_transformation,[],[f37]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_259,plain,
% 2.89/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.89/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7774,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_259,c_4462]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_12,negated_conjecture,
% 2.89/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.89/0.96      inference(cnf_transformation,[],[f38]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_260,plain,
% 2.89/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.89/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7773,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_260,c_4462]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4,plain,
% 2.89/0.96      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.89/0.96      inference(cnf_transformation,[],[f30]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1,plain,
% 2.89/0.96      ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 ),
% 2.89/0.96      inference(cnf_transformation,[],[f44]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_680,plain,
% 2.89/0.96      ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_8,plain,
% 2.89/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.89/0.96      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.89/0.96      inference(cnf_transformation,[],[f48]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_261,plain,
% 2.89/0.96      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.89/0.96      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.89/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_689,plain,
% 2.89/0.96      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_272,c_261]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1171,plain,
% 2.89/0.96      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_689]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2422,plain,
% 2.89/0.96      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_680,c_1171]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2420,plain,
% 2.89/0.96      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1,c_1171]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_3895,plain,
% 2.89/0.96      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_2420]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7571,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_2422,c_3895]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7569,plain,
% 2.89/0.96      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_2422]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7559,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_3895,c_2422]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_0,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 2.89/0.96      inference(cnf_transformation,[],[f43]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_577,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_881,plain,
% 2.89/0.96      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_577,c_1]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1332,plain,
% 2.89/0.96      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_881,c_689]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2,plain,
% 2.89/0.96      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
% 2.89/0.96      inference(cnf_transformation,[],[f45]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_283,plain,
% 2.89/0.96      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.89/0.96      inference(light_normalisation,[status(thm)],[c_2,c_1]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1340,plain,
% 2.89/0.96      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_1332,c_283]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_3,plain,
% 2.89/0.96      ( ~ r1_xboole_0(X0,X1)
% 2.89/0.96      | k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X2,X1)),X0))) = k3_tarski(k2_tarski(k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0))),X1)) ),
% 2.89/0.96      inference(cnf_transformation,[],[f46]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_10,negated_conjecture,
% 2.89/0.96      ( r1_xboole_0(sK1,sK2) ),
% 2.89/0.96      inference(cnf_transformation,[],[f40]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_99,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))),X1))
% 2.89/0.96      | sK2 != X1
% 2.89/0.96      | sK1 != X2 ),
% 2.89/0.96      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_100,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(X0,sK2)),k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,sK2)),sK1))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))),sK2)) ),
% 2.89/0.96      inference(unflattening,[status(thm)],[c_99]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_575,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(X0,sK2)),k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(X0,sK2))))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))),sK2)) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_4,c_100]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_962,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),sK2)) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK1,sK2))) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_577,c_575]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_566,plain,
% 2.89/0.96      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_260,c_261]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_887,plain,
% 2.89/0.96      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(X0,sK2))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_566]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1066,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),sK2)) = k7_subset_1(u1_struct_0(sK0),sK2,sK1) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_962,c_887]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1068,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(sK2,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,sK1))))) = k7_subset_1(u1_struct_0(sK0),sK2,sK1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_1066]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1141,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_689,c_566]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2539,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(sK2,k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))) = k7_subset_1(sK2,sK2,sK1) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_1068,c_689,c_1141]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7092,plain,
% 2.89/0.96      ( k7_subset_1(sK2,sK2,sK1) = k3_tarski(k2_tarski(sK2,k1_xboole_0)) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_1340,c_2539]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_7094,plain,
% 2.89/0.96      ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_7092,c_0]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4460,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))
% 2.89/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_260,c_262]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4551,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_259,c_4460]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_11,negated_conjecture,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 2.89/0.96      inference(cnf_transformation,[],[f39]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4556,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
% 2.89/0.96      inference(light_normalisation,[status(thm)],[c_4551,c_11]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4728,plain,
% 2.89/0.96      ( k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) = sK2 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4556,c_680]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_5120,plain,
% 2.89/0.96      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = k5_xboole_0(k2_struct_0(sK0),sK2) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4728,c_1171]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4715,plain,
% 2.89/0.96      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4556,c_3895]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_6763,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = k5_xboole_0(k2_struct_0(sK0),sK2) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_5120,c_4715]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4461,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),X0,sK1) = k3_tarski(k2_tarski(X0,sK1))
% 2.89/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_259,c_262]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_6192,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_272,c_4461]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_6191,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_259,c_4461]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_6190,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_260,c_4461]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1140,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(X0,sK2)),k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(X0,sK2))))) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_689,c_575]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2427,plain,
% 2.89/0.96      ( k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1171,c_1140]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4720,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(k7_subset_1(sK1,sK1,sK1),sK2)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4556,c_2427]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_567,plain,
% 2.89/0.96      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_259,c_261]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_947,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k3_tarski(k2_tarski(sK1,X0))) = k5_xboole_0(sK1,sK1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1,c_567]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_953,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k3_tarski(k2_tarski(sK1,X0))) = k1_xboole_0 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_947,c_283]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1142,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_689,c_567]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2931,plain,
% 2.89/0.96      ( k7_subset_1(sK1,sK1,k3_tarski(k2_tarski(sK1,X0))) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_953,c_1142]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2939,plain,
% 2.89/0.96      ( k7_subset_1(sK1,sK1,sK1) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_0,c_2931]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4744,plain,
% 2.89/0.96      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k3_tarski(k2_tarski(k1_xboole_0,sK2)) ),
% 2.89/0.96      inference(light_normalisation,[status(thm)],[c_4720,c_2939]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4745,plain,
% 2.89/0.96      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_4744,c_577]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4727,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4556,c_953]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4726,plain,
% 2.89/0.96      ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4556,c_2931]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_886,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK2,k3_tarski(k2_tarski(sK2,X0))) = k5_xboole_0(sK2,sK2) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1,c_566]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_892,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK2,k3_tarski(k2_tarski(sK2,X0))) = k1_xboole_0 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_886,c_283]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2054,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK2,k3_tarski(k2_tarski(X0,sK2))) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_892]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4723,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4556,c_2054]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2069,plain,
% 2.89/0.96      ( k7_subset_1(sK2,sK2,k3_tarski(k2_tarski(X0,sK2))) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_2054,c_1141]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4722,plain,
% 2.89/0.96      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4556,c_2069]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4719,plain,
% 2.89/0.96      ( k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) = sK1 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4556,c_1]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_961,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))),sK2)) = k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1,c_575]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_970,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK1),sK2)) = k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_961,c_567]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1055,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK1))) = k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_970]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2439,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(sK2,k7_subset_1(sK1,sK1,sK1))) = k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_1055,c_1142]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_3286,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k1_xboole_0)) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_2939,c_2439]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_3291,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = sK2 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_3286,c_0]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4714,plain,
% 2.89/0.96      ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_4556,c_3291]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4552,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_272,c_4460]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_4550,plain,
% 2.89/0.96      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_260,c_4460]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_963,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,X0)),k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK2,X0))))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))),sK2)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_575]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1139,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,X0)),k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK2,X0))))) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_689,c_963]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_3648,plain,
% 2.89/0.96      ( k3_tarski(k2_tarski(k7_subset_1(sK1,sK1,sK1),sK2)) = k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_680,c_1139]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_3655,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = k3_tarski(k2_tarski(k1_xboole_0,sK2)) ),
% 2.89/0.96      inference(light_normalisation,[status(thm)],[c_3648,c_2939]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_3656,plain,
% 2.89/0.96      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = sK2 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_3655,c_577]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_3637,plain,
% 2.89/0.96      ( k7_subset_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK2,X0)),sK1) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_2427]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2940,plain,
% 2.89/0.96      ( k7_subset_1(sK1,sK1,k3_tarski(k2_tarski(X0,sK1))) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_2931]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2929,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k3_tarski(k2_tarski(X0,sK1))) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_953]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2056,plain,
% 2.89/0.96      ( k7_subset_1(sK2,sK2,k3_tarski(k2_tarski(sK2,X0))) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_892,c_1141]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_2769,plain,
% 2.89/0.96      ( k7_subset_1(sK2,sK2,sK2) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_0,c_2056]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1334,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = k5_xboole_0(sK2,k1_xboole_0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_881,c_887]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1960,plain,
% 2.89/0.96      ( k7_subset_1(sK2,sK2,k1_xboole_0) = k5_xboole_0(sK2,k1_xboole_0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1141,c_1334]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_948,plain,
% 2.89/0.96      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_567]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1333,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_881,c_948]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1820,plain,
% 2.89/0.96      ( k7_subset_1(sK1,sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1142,c_1333]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1406,plain,
% 2.89/0.96      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(X0,X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_680,c_689]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1408,plain,
% 2.89/0.96      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 2.89/0.96      inference(light_normalisation,[status(thm)],[c_1406,c_283]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1330,plain,
% 2.89/0.96      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_4,c_881]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1396,plain,
% 2.89/0.96      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1330,c_689]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_679,plain,
% 2.89/0.96      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1316,plain,
% 2.89/0.96      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_679,c_689]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1326,plain,
% 2.89/0.96      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 2.89/0.96      inference(light_normalisation,[status(thm)],[c_1316,c_283]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1317,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_679,c_948]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1323,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_xboole_0 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_1317,c_283]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1318,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k5_xboole_0(sK2,sK2) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_679,c_887]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1320,plain,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),sK2,sK2) = k1_xboole_0 ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_1318,c_283]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1170,plain,
% 2.89/0.96      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0) ),
% 2.89/0.96      inference(superposition,[status(thm)],[c_1,c_689]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1182,plain,
% 2.89/0.96      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 2.89/0.96      inference(light_normalisation,[status(thm)],[c_1170,c_283]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_1138,plain,
% 2.89/0.96      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 2.89/0.96      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.89/0.96      inference(demodulation,[status(thm)],[c_689,c_261]) ).
% 2.89/0.96  
% 2.89/0.96  cnf(c_9,negated_conjecture,
% 2.89/0.96      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 2.89/0.96      inference(cnf_transformation,[],[f41]) ).
% 2.89/0.96  
% 2.89/0.96  
% 2.89/0.96  % SZS output end Saturation for theBenchmark.p
% 2.89/0.96  
% 2.89/0.96  ------                               Statistics
% 2.89/0.96  
% 2.89/0.96  ------ General
% 2.89/0.96  
% 2.89/0.96  abstr_ref_over_cycles:                  0
% 2.89/0.96  abstr_ref_under_cycles:                 0
% 2.89/0.96  gc_basic_clause_elim:                   0
% 2.89/0.96  forced_gc_time:                         0
% 2.89/0.96  parsing_time:                           0.008
% 2.89/0.96  unif_index_cands_time:                  0.
% 2.89/0.96  unif_index_add_time:                    0.
% 2.89/0.96  orderings_time:                         0.
% 2.89/0.96  out_proof_time:                         0.
% 2.89/0.96  total_time:                             0.325
% 2.89/0.96  num_of_symbols:                         47
% 2.89/0.96  num_of_terms:                           7252
% 2.89/0.96  
% 2.89/0.96  ------ Preprocessing
% 2.89/0.96  
% 2.89/0.96  num_of_splits:                          0
% 2.89/0.96  num_of_split_atoms:                     0
% 2.89/0.96  num_of_reused_defs:                     0
% 2.89/0.96  num_eq_ax_congr_red:                    3
% 2.89/0.96  num_of_sem_filtered_clauses:            1
% 2.89/0.96  num_of_subtypes:                        0
% 2.89/0.96  monotx_restored_types:                  0
% 2.89/0.96  sat_num_of_epr_types:                   0
% 2.89/0.96  sat_num_of_non_cyclic_types:            0
% 2.89/0.96  sat_guarded_non_collapsed_types:        0
% 2.89/0.96  num_pure_diseq_elim:                    0
% 2.89/0.96  simp_replaced_by:                       0
% 2.89/0.96  res_preprocessed:                       78
% 2.89/0.96  prep_upred:                             0
% 2.89/0.96  prep_unflattend:                        2
% 2.89/0.96  smt_new_axioms:                         0
% 2.89/0.96  pred_elim_cands:                        1
% 2.89/0.96  pred_elim:                              1
% 2.89/0.96  pred_elim_cl:                           1
% 2.89/0.96  pred_elim_cycles:                       3
% 2.89/0.96  merged_defs:                            0
% 2.89/0.96  merged_defs_ncl:                        0
% 2.89/0.96  bin_hyper_res:                          0
% 2.89/0.96  prep_cycles:                            4
% 2.89/0.96  pred_elim_time:                         0.
% 2.89/0.96  splitting_time:                         0.
% 2.89/0.96  sem_filter_time:                        0.
% 2.89/0.96  monotx_time:                            0.
% 2.89/0.96  subtype_inf_time:                       0.
% 2.89/0.96  
% 2.89/0.96  ------ Problem properties
% 2.89/0.96  
% 2.89/0.96  clauses:                                13
% 2.89/0.96  conjectures:                            4
% 2.89/0.96  epr:                                    0
% 2.89/0.96  horn:                                   13
% 2.89/0.96  ground:                                 4
% 2.89/0.96  unary:                                  11
% 2.89/0.96  binary:                                 1
% 2.89/0.96  lits:                                   16
% 2.89/0.96  lits_eq:                                10
% 2.89/0.96  fd_pure:                                0
% 2.89/0.96  fd_pseudo:                              0
% 2.89/0.96  fd_cond:                                0
% 2.89/0.96  fd_pseudo_cond:                         0
% 2.89/0.96  ac_symbols:                             0
% 2.89/0.96  
% 2.89/0.96  ------ Propositional Solver
% 2.89/0.96  
% 2.89/0.96  prop_solver_calls:                      29
% 2.89/0.96  prop_fast_solver_calls:                 412
% 2.89/0.96  smt_solver_calls:                       0
% 2.89/0.96  smt_fast_solver_calls:                  0
% 2.89/0.96  prop_num_of_clauses:                    3351
% 2.89/0.96  prop_preprocess_simplified:             6946
% 2.89/0.96  prop_fo_subsumed:                       0
% 2.89/0.96  prop_solver_time:                       0.
% 2.89/0.96  smt_solver_time:                        0.
% 2.89/0.96  smt_fast_solver_time:                   0.
% 2.89/0.96  prop_fast_solver_time:                  0.
% 2.89/0.96  prop_unsat_core_time:                   0.
% 2.89/0.96  
% 2.89/0.96  ------ QBF
% 2.89/0.96  
% 2.89/0.96  qbf_q_res:                              0
% 2.89/0.96  qbf_num_tautologies:                    0
% 2.89/0.96  qbf_prep_cycles:                        0
% 2.89/0.96  
% 2.89/0.96  ------ BMC1
% 2.89/0.96  
% 2.89/0.96  bmc1_current_bound:                     -1
% 2.89/0.96  bmc1_last_solved_bound:                 -1
% 2.89/0.96  bmc1_unsat_core_size:                   -1
% 2.89/0.96  bmc1_unsat_core_parents_size:           -1
% 2.89/0.96  bmc1_merge_next_fun:                    0
% 2.89/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.89/0.96  
% 2.89/0.96  ------ Instantiation
% 2.89/0.96  
% 2.89/0.96  inst_num_of_clauses:                    1264
% 2.89/0.96  inst_num_in_passive:                    451
% 2.89/0.96  inst_num_in_active:                     513
% 2.89/0.96  inst_num_in_unprocessed:                300
% 2.89/0.96  inst_num_of_loops:                      520
% 2.89/0.96  inst_num_of_learning_restarts:          0
% 2.89/0.96  inst_num_moves_active_passive:          4
% 2.89/0.96  inst_lit_activity:                      0
% 2.89/0.96  inst_lit_activity_moves:                0
% 2.89/0.96  inst_num_tautologies:                   0
% 2.89/0.96  inst_num_prop_implied:                  0
% 2.89/0.96  inst_num_existing_simplified:           0
% 2.89/0.96  inst_num_eq_res_simplified:             0
% 2.89/0.96  inst_num_child_elim:                    0
% 2.89/0.96  inst_num_of_dismatching_blockings:      408
% 2.89/0.96  inst_num_of_non_proper_insts:           1005
% 2.89/0.96  inst_num_of_duplicates:                 0
% 2.89/0.96  inst_inst_num_from_inst_to_res:         0
% 2.89/0.96  inst_dismatching_checking_time:         0.
% 2.89/0.96  
% 2.89/0.96  ------ Resolution
% 2.89/0.96  
% 2.89/0.96  res_num_of_clauses:                     0
% 2.89/0.96  res_num_in_passive:                     0
% 2.89/0.96  res_num_in_active:                      0
% 2.89/0.96  res_num_of_loops:                       82
% 2.89/0.96  res_forward_subset_subsumed:            111
% 2.89/0.96  res_backward_subset_subsumed:           0
% 2.89/0.96  res_forward_subsumed:                   0
% 2.89/0.96  res_backward_subsumed:                  0
% 2.89/0.96  res_forward_subsumption_resolution:     0
% 2.89/0.96  res_backward_subsumption_resolution:    0
% 2.89/0.96  res_clause_to_clause_subsumption:       291
% 2.89/0.96  res_orphan_elimination:                 0
% 2.89/0.96  res_tautology_del:                      117
% 2.89/0.96  res_num_eq_res_simplified:              0
% 2.89/0.96  res_num_sel_changes:                    0
% 2.89/0.96  res_moves_from_active_to_pass:          0
% 2.89/0.96  
% 2.89/0.96  ------ Superposition
% 2.89/0.96  
% 2.89/0.96  sup_time_total:                         0.
% 2.89/0.96  sup_time_generating:                    0.
% 2.89/0.96  sup_time_sim_full:                      0.
% 2.89/0.96  sup_time_sim_immed:                     0.
% 2.89/0.96  
% 2.89/0.96  sup_num_of_clauses:                     108
% 2.89/0.96  sup_num_in_active:                      76
% 2.89/0.96  sup_num_in_passive:                     32
% 2.89/0.96  sup_num_of_loops:                       103
% 2.89/0.96  sup_fw_superposition:                   237
% 2.89/0.96  sup_bw_superposition:                   125
% 2.89/0.96  sup_immediate_simplified:               59
% 2.89/0.96  sup_given_eliminated:                   0
% 2.89/0.96  comparisons_done:                       0
% 2.89/0.96  comparisons_avoided:                    0
% 2.89/0.96  
% 2.89/0.96  ------ Simplifications
% 2.89/0.96  
% 2.89/0.96  
% 2.89/0.96  sim_fw_subset_subsumed:                 0
% 2.89/0.96  sim_bw_subset_subsumed:                 0
% 2.89/0.96  sim_fw_subsumed:                        16
% 2.89/0.96  sim_bw_subsumed:                        0
% 2.89/0.96  sim_fw_subsumption_res:                 0
% 2.89/0.96  sim_bw_subsumption_res:                 0
% 2.89/0.96  sim_tautology_del:                      0
% 2.89/0.96  sim_eq_tautology_del:                   29
% 2.89/0.96  sim_eq_res_simp:                        0
% 2.89/0.96  sim_fw_demodulated:                     44
% 2.89/0.96  sim_bw_demodulated:                     30
% 2.89/0.96  sim_light_normalised:                   60
% 2.89/0.96  sim_joinable_taut:                      0
% 2.89/0.96  sim_joinable_simp:                      0
% 2.89/0.96  sim_ac_normalised:                      0
% 2.89/0.96  sim_smt_subsumption:                    0
% 2.89/0.96  
%------------------------------------------------------------------------------
