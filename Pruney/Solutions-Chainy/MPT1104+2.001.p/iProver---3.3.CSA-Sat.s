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
% DateTime   : Thu Dec  3 12:11:08 EST 2020

% Result     : CounterSatisfiable 3.00s
% Output     : Saturation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  194 (4460 expanded)
%              Number of clauses        :  136 (1139 expanded)
%              Number of leaves         :   18 (1184 expanded)
%              Depth                    :   17
%              Number of atoms          :  295 (9541 expanded)
%              Number of equality atoms :  217 (5474 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f49,f50])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f29,f50,f50])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f28,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f46,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_136,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_804,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_461,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1984,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_461])).

cnf(c_9,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_457,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_472,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_457,c_8])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_455,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_930,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_472,c_455])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_458,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3528,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1))) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_930,c_458])).

cnf(c_3568,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3528,c_930])).

cnf(c_6968,plain,
    ( k7_subset_1(k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1984,c_3568])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1154,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_804,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_479,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_4])).

cnf(c_1157,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1154,c_4,c_479])).

cnf(c_1158,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1157,c_479])).

cnf(c_3586,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_930])).

cnf(c_3618,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3586,c_479])).

cnf(c_6970,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6968,c_1158,c_3618])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_456,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1649,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_456])).

cnf(c_5269,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1649,c_930])).

cnf(c_5275,plain,
    ( k5_xboole_0(X0,k7_subset_1(X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_472,c_5269])).

cnf(c_7050,plain,
    ( k4_subset_1(X0,X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6970,c_5275])).

cnf(c_7051,plain,
    ( k4_subset_1(X0,X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7050,c_479])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_452,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_796,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_452,c_455])).

cnf(c_1285,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(superposition,[status(thm)],[c_796,c_0])).

cnf(c_1553,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(sK1,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1285])).

cnf(c_3595,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_930,c_1553])).

cnf(c_1648,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_452,c_456])).

cnf(c_1656,plain,
    ( k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1648,c_1285])).

cnf(c_2201,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_452,c_1656])).

cnf(c_3597,plain,
    ( k5_xboole_0(sK1,k7_subset_1(sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3595,c_2201])).

cnf(c_5441,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_5275,c_3597])).

cnf(c_7055,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_7051,c_5441])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_453,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_795,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(superposition,[status(thm)],[c_453,c_455])).

cnf(c_1165,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
    inference(superposition,[status(thm)],[c_795,c_0])).

cnf(c_1425,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1165])).

cnf(c_3594,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK2,sK2)) = k5_xboole_0(sK2,k7_subset_1(sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_930,c_1425])).

cnf(c_1647,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_456])).

cnf(c_1661,plain,
    ( k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1647,c_1165])).

cnf(c_2369,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
    inference(superposition,[status(thm)],[c_453,c_1661])).

cnf(c_3600,plain,
    ( k5_xboole_0(sK2,k7_subset_1(sK2,sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3594,c_2369])).

cnf(c_5440,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_5275,c_3600])).

cnf(c_7054,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_7051,c_5440])).

cnf(c_5449,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5275,c_1158])).

cnf(c_3589,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_804,c_930])).

cnf(c_3609,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3589,c_479])).

cnf(c_5451,plain,
    ( k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5449,c_3609])).

cnf(c_3529,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_930,c_456])).

cnf(c_5423,plain,
    ( k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_452,c_3529])).

cnf(c_5422,plain,
    ( k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_3529])).

cnf(c_5273,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_453,c_5269])).

cnf(c_2371,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_472,c_1661])).

cnf(c_3533,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_930,c_795])).

cnf(c_4944,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_2371,c_3533])).

cnf(c_5282,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5273,c_4944])).

cnf(c_5274,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_452,c_5269])).

cnf(c_2202,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_472,c_1656])).

cnf(c_3534,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_930,c_796])).

cnf(c_4855,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_2202,c_3534])).

cnf(c_5279,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5274,c_4855])).

cnf(c_3530,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_930,c_0])).

cnf(c_3558,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3530,c_930])).

cnf(c_5054,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_3558,c_4944])).

cnf(c_5053,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_3558,c_4855])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_454,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2479,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))),sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_454,c_458])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_459,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1894,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_459])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_460,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2072,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1894,c_460])).

cnf(c_2490,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)),sK2))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2479,c_2072])).

cnf(c_2491,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK2),sK2))) = sK1 ),
    inference(demodulation,[status(thm)],[c_2490,c_479])).

cnf(c_2151,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2072,c_1285])).

cnf(c_1423,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_796,c_1165])).

cnf(c_2154,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2151,c_479,c_1423])).

cnf(c_1899,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_460])).

cnf(c_2080,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1899,c_796])).

cnf(c_2091,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2080,c_479])).

cnf(c_2200,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_453,c_1656])).

cnf(c_14,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2208,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2200,c_14])).

cnf(c_3350,plain,
    ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2091,c_2208])).

cnf(c_3525,plain,
    ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2154,c_2091,c_3350])).

cnf(c_4845,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2491,c_3525])).

cnf(c_4848,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) = sK1 ),
    inference(superposition,[status(thm)],[c_7,c_4845])).

cnf(c_4850,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_4845,c_930])).

cnf(c_2481,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2)))),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2)))),sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_1894,c_458])).

cnf(c_2483,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)),sK1))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2481,c_1899])).

cnf(c_2484,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,sK1),sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_2483,c_479])).

cnf(c_4577,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2484,c_3350])).

cnf(c_4580,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) = sK2 ),
    inference(superposition,[status(thm)],[c_7,c_4577])).

cnf(c_4582,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_4577,c_930])).

cnf(c_1282,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_796])).

cnf(c_1292,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_1282,c_479])).

cnf(c_3839,plain,
    ( k7_subset_1(sK1,sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_3534,c_1292])).

cnf(c_3828,plain,
    ( k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3534,c_1656])).

cnf(c_1162,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_795])).

cnf(c_1172,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = sK2 ),
    inference(demodulation,[status(thm)],[c_1162,c_479])).

cnf(c_3823,plain,
    ( k7_subset_1(sK2,sK2,k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_3533,c_1172])).

cnf(c_3812,plain,
    ( k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3533,c_1661])).

cnf(c_3587,plain,
    ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1899,c_930])).

cnf(c_3615,plain,
    ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_3587,c_479])).

cnf(c_3588,plain,
    ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2072,c_930])).

cnf(c_3612,plain,
    ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_3588,c_479])).

cnf(c_3590,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_930])).

cnf(c_3532,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_930,c_455])).

cnf(c_2370,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(superposition,[status(thm)],[c_452,c_1661])).

cnf(c_2079,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1899,c_0])).

cnf(c_2094,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_2079,c_479,c_795,c_1285])).

cnf(c_2375,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2370,c_2094])).

cnf(c_3437,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3350,c_2375])).

cnf(c_1163,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(X0,sK2))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(superposition,[status(thm)],[c_7,c_795])).

cnf(c_2082,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1899,c_1163])).

cnf(c_2084,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_2082,c_479])).

cnf(c_1985,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_461])).

cnf(c_1983,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_461])).

cnf(c_12,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.00/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/0.99  
% 3.00/0.99  ------  iProver source info
% 3.00/0.99  
% 3.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/0.99  git: non_committed_changes: false
% 3.00/0.99  git: last_make_outside_of_git: false
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/0.99  --trig_cnt_out                          false
% 3.00/0.99  --trig_cnt_out_tolerance                1.
% 3.00/0.99  --trig_cnt_out_sk_spl                   false
% 3.00/0.99  --abstr_cl_out                          false
% 3.00/0.99  
% 3.00/0.99  ------ Global Options
% 3.00/0.99  
% 3.00/0.99  --schedule                              default
% 3.00/0.99  --add_important_lit                     false
% 3.00/0.99  --prop_solver_per_cl                    1000
% 3.00/0.99  --min_unsat_core                        false
% 3.00/0.99  --soft_assumptions                      false
% 3.00/0.99  --soft_lemma_size                       3
% 3.00/0.99  --prop_impl_unit_size                   0
% 3.00/0.99  --prop_impl_unit                        []
% 3.00/0.99  --share_sel_clauses                     true
% 3.00/0.99  --reset_solvers                         false
% 3.00/0.99  --bc_imp_inh                            [conj_cone]
% 3.00/0.99  --conj_cone_tolerance                   3.
% 3.00/0.99  --extra_neg_conj                        none
% 3.00/0.99  --large_theory_mode                     true
% 3.00/0.99  --prolific_symb_bound                   200
% 3.00/0.99  --lt_threshold                          2000
% 3.00/0.99  --clause_weak_htbl                      true
% 3.00/0.99  --gc_record_bc_elim                     false
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing Options
% 3.00/0.99  
% 3.00/0.99  --preprocessing_flag                    true
% 3.00/0.99  --time_out_prep_mult                    0.1
% 3.00/0.99  --splitting_mode                        input
% 3.00/0.99  --splitting_grd                         true
% 3.00/0.99  --splitting_cvd                         false
% 3.00/0.99  --splitting_cvd_svl                     false
% 3.00/0.99  --splitting_nvd                         32
% 3.00/0.99  --sub_typing                            true
% 3.00/0.99  --prep_gs_sim                           true
% 3.00/0.99  --prep_unflatten                        true
% 3.00/0.99  --prep_res_sim                          true
% 3.00/0.99  --prep_upred                            true
% 3.00/0.99  --prep_sem_filter                       exhaustive
% 3.00/0.99  --prep_sem_filter_out                   false
% 3.00/0.99  --pred_elim                             true
% 3.00/0.99  --res_sim_input                         true
% 3.00/0.99  --eq_ax_congr_red                       true
% 3.00/0.99  --pure_diseq_elim                       true
% 3.00/0.99  --brand_transform                       false
% 3.00/0.99  --non_eq_to_eq                          false
% 3.00/0.99  --prep_def_merge                        true
% 3.00/0.99  --prep_def_merge_prop_impl              false
% 3.00/0.99  --prep_def_merge_mbd                    true
% 3.00/0.99  --prep_def_merge_tr_red                 false
% 3.00/0.99  --prep_def_merge_tr_cl                  false
% 3.00/0.99  --smt_preprocessing                     true
% 3.00/0.99  --smt_ac_axioms                         fast
% 3.00/0.99  --preprocessed_out                      false
% 3.00/0.99  --preprocessed_stats                    false
% 3.00/0.99  
% 3.00/0.99  ------ Abstraction refinement Options
% 3.00/0.99  
% 3.00/0.99  --abstr_ref                             []
% 3.00/0.99  --abstr_ref_prep                        false
% 3.00/0.99  --abstr_ref_until_sat                   false
% 3.00/0.99  --abstr_ref_sig_restrict                funpre
% 3.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.99  --abstr_ref_under                       []
% 3.00/0.99  
% 3.00/0.99  ------ SAT Options
% 3.00/0.99  
% 3.00/0.99  --sat_mode                              false
% 3.00/0.99  --sat_fm_restart_options                ""
% 3.00/0.99  --sat_gr_def                            false
% 3.00/0.99  --sat_epr_types                         true
% 3.00/0.99  --sat_non_cyclic_types                  false
% 3.00/0.99  --sat_finite_models                     false
% 3.00/0.99  --sat_fm_lemmas                         false
% 3.00/0.99  --sat_fm_prep                           false
% 3.00/0.99  --sat_fm_uc_incr                        true
% 3.00/0.99  --sat_out_model                         small
% 3.00/0.99  --sat_out_clauses                       false
% 3.00/0.99  
% 3.00/0.99  ------ QBF Options
% 3.00/0.99  
% 3.00/0.99  --qbf_mode                              false
% 3.00/0.99  --qbf_elim_univ                         false
% 3.00/0.99  --qbf_dom_inst                          none
% 3.00/0.99  --qbf_dom_pre_inst                      false
% 3.00/0.99  --qbf_sk_in                             false
% 3.00/0.99  --qbf_pred_elim                         true
% 3.00/0.99  --qbf_split                             512
% 3.00/0.99  
% 3.00/0.99  ------ BMC1 Options
% 3.00/0.99  
% 3.00/0.99  --bmc1_incremental                      false
% 3.00/0.99  --bmc1_axioms                           reachable_all
% 3.00/0.99  --bmc1_min_bound                        0
% 3.00/0.99  --bmc1_max_bound                        -1
% 3.00/0.99  --bmc1_max_bound_default                -1
% 3.00/0.99  --bmc1_symbol_reachability              true
% 3.00/0.99  --bmc1_property_lemmas                  false
% 3.00/0.99  --bmc1_k_induction                      false
% 3.00/0.99  --bmc1_non_equiv_states                 false
% 3.00/0.99  --bmc1_deadlock                         false
% 3.00/0.99  --bmc1_ucm                              false
% 3.00/0.99  --bmc1_add_unsat_core                   none
% 3.00/0.99  --bmc1_unsat_core_children              false
% 3.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.99  --bmc1_out_stat                         full
% 3.00/0.99  --bmc1_ground_init                      false
% 3.00/0.99  --bmc1_pre_inst_next_state              false
% 3.00/0.99  --bmc1_pre_inst_state                   false
% 3.00/0.99  --bmc1_pre_inst_reach_state             false
% 3.00/0.99  --bmc1_out_unsat_core                   false
% 3.00/0.99  --bmc1_aig_witness_out                  false
% 3.00/0.99  --bmc1_verbose                          false
% 3.00/0.99  --bmc1_dump_clauses_tptp                false
% 3.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.99  --bmc1_dump_file                        -
% 3.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.99  --bmc1_ucm_extend_mode                  1
% 3.00/0.99  --bmc1_ucm_init_mode                    2
% 3.00/0.99  --bmc1_ucm_cone_mode                    none
% 3.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.99  --bmc1_ucm_relax_model                  4
% 3.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.99  --bmc1_ucm_layered_model                none
% 3.00/0.99  --bmc1_ucm_max_lemma_size               10
% 3.00/0.99  
% 3.00/0.99  ------ AIG Options
% 3.00/0.99  
% 3.00/0.99  --aig_mode                              false
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation Options
% 3.00/0.99  
% 3.00/0.99  --instantiation_flag                    true
% 3.00/0.99  --inst_sos_flag                         false
% 3.00/0.99  --inst_sos_phase                        true
% 3.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel_side                     num_symb
% 3.00/0.99  --inst_solver_per_active                1400
% 3.00/0.99  --inst_solver_calls_frac                1.
% 3.00/0.99  --inst_passive_queue_type               priority_queues
% 3.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.99  --inst_passive_queues_freq              [25;2]
% 3.00/0.99  --inst_dismatching                      true
% 3.00/0.99  --inst_eager_unprocessed_to_passive     true
% 3.00/0.99  --inst_prop_sim_given                   true
% 3.00/0.99  --inst_prop_sim_new                     false
% 3.00/0.99  --inst_subs_new                         false
% 3.00/0.99  --inst_eq_res_simp                      false
% 3.00/0.99  --inst_subs_given                       false
% 3.00/0.99  --inst_orphan_elimination               true
% 3.00/0.99  --inst_learning_loop_flag               true
% 3.00/0.99  --inst_learning_start                   3000
% 3.00/0.99  --inst_learning_factor                  2
% 3.00/0.99  --inst_start_prop_sim_after_learn       3
% 3.00/0.99  --inst_sel_renew                        solver
% 3.00/0.99  --inst_lit_activity_flag                true
% 3.00/0.99  --inst_restr_to_given                   false
% 3.00/0.99  --inst_activity_threshold               500
% 3.00/0.99  --inst_out_proof                        true
% 3.00/0.99  
% 3.00/0.99  ------ Resolution Options
% 3.00/0.99  
% 3.00/0.99  --resolution_flag                       true
% 3.00/0.99  --res_lit_sel                           adaptive
% 3.00/0.99  --res_lit_sel_side                      none
% 3.00/0.99  --res_ordering                          kbo
% 3.00/0.99  --res_to_prop_solver                    active
% 3.00/0.99  --res_prop_simpl_new                    false
% 3.00/0.99  --res_prop_simpl_given                  true
% 3.00/0.99  --res_passive_queue_type                priority_queues
% 3.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.99  --res_passive_queues_freq               [15;5]
% 3.00/0.99  --res_forward_subs                      full
% 3.00/0.99  --res_backward_subs                     full
% 3.00/0.99  --res_forward_subs_resolution           true
% 3.00/0.99  --res_backward_subs_resolution          true
% 3.00/0.99  --res_orphan_elimination                true
% 3.00/0.99  --res_time_limit                        2.
% 3.00/0.99  --res_out_proof                         true
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Options
% 3.00/0.99  
% 3.00/0.99  --superposition_flag                    true
% 3.00/0.99  --sup_passive_queue_type                priority_queues
% 3.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.99  --demod_completeness_check              fast
% 3.00/0.99  --demod_use_ground                      true
% 3.00/0.99  --sup_to_prop_solver                    passive
% 3.00/0.99  --sup_prop_simpl_new                    true
% 3.00/0.99  --sup_prop_simpl_given                  true
% 3.00/0.99  --sup_fun_splitting                     false
% 3.00/0.99  --sup_smt_interval                      50000
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Simplification Setup
% 3.00/0.99  
% 3.00/0.99  --sup_indices_passive                   []
% 3.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_full_bw                           [BwDemod]
% 3.00/0.99  --sup_immed_triv                        [TrivRules]
% 3.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_immed_bw_main                     []
% 3.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  
% 3.00/0.99  ------ Combination Options
% 3.00/0.99  
% 3.00/0.99  --comb_res_mult                         3
% 3.00/0.99  --comb_sup_mult                         2
% 3.00/0.99  --comb_inst_mult                        10
% 3.00/0.99  
% 3.00/0.99  ------ Debug Options
% 3.00/0.99  
% 3.00/0.99  --dbg_backtrace                         false
% 3.00/0.99  --dbg_dump_prop_clauses                 false
% 3.00/0.99  --dbg_dump_prop_clauses_file            -
% 3.00/0.99  --dbg_out_stat                          false
% 3.00/0.99  ------ Parsing...
% 3.00/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/0.99  ------ Proving...
% 3.00/0.99  ------ Problem Properties 
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  clauses                                 17
% 3.00/0.99  conjectures                             5
% 3.00/0.99  EPR                                     2
% 3.00/0.99  Horn                                    17
% 3.00/0.99  unary                                   11
% 3.00/0.99  binary                                  5
% 3.00/0.99  lits                                    24
% 3.00/0.99  lits eq                                 12
% 3.00/0.99  fd_pure                                 0
% 3.00/0.99  fd_pseudo                               0
% 3.00/0.99  fd_cond                                 0
% 3.00/0.99  fd_pseudo_cond                          0
% 3.00/0.99  AC symbols                              0
% 3.00/0.99  
% 3.00/0.99  ------ Schedule dynamic 5 is on 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  ------ 
% 3.00/0.99  Current options:
% 3.00/0.99  ------ 
% 3.00/0.99  
% 3.00/0.99  ------ Input Options
% 3.00/0.99  
% 3.00/0.99  --out_options                           all
% 3.00/0.99  --tptp_safe_out                         true
% 3.00/0.99  --problem_path                          ""
% 3.00/0.99  --include_path                          ""
% 3.00/0.99  --clausifier                            res/vclausify_rel
% 3.00/0.99  --clausifier_options                    --mode clausify
% 3.00/0.99  --stdin                                 false
% 3.00/0.99  --stats_out                             all
% 3.00/0.99  
% 3.00/0.99  ------ General Options
% 3.00/0.99  
% 3.00/0.99  --fof                                   false
% 3.00/0.99  --time_out_real                         305.
% 3.00/0.99  --time_out_virtual                      -1.
% 3.00/0.99  --symbol_type_check                     false
% 3.00/0.99  --clausify_out                          false
% 3.00/0.99  --sig_cnt_out                           false
% 3.00/0.99  --trig_cnt_out                          false
% 3.00/0.99  --trig_cnt_out_tolerance                1.
% 3.00/0.99  --trig_cnt_out_sk_spl                   false
% 3.00/0.99  --abstr_cl_out                          false
% 3.00/0.99  
% 3.00/0.99  ------ Global Options
% 3.00/0.99  
% 3.00/0.99  --schedule                              default
% 3.00/0.99  --add_important_lit                     false
% 3.00/0.99  --prop_solver_per_cl                    1000
% 3.00/0.99  --min_unsat_core                        false
% 3.00/0.99  --soft_assumptions                      false
% 3.00/0.99  --soft_lemma_size                       3
% 3.00/0.99  --prop_impl_unit_size                   0
% 3.00/0.99  --prop_impl_unit                        []
% 3.00/0.99  --share_sel_clauses                     true
% 3.00/0.99  --reset_solvers                         false
% 3.00/0.99  --bc_imp_inh                            [conj_cone]
% 3.00/0.99  --conj_cone_tolerance                   3.
% 3.00/0.99  --extra_neg_conj                        none
% 3.00/0.99  --large_theory_mode                     true
% 3.00/0.99  --prolific_symb_bound                   200
% 3.00/0.99  --lt_threshold                          2000
% 3.00/0.99  --clause_weak_htbl                      true
% 3.00/0.99  --gc_record_bc_elim                     false
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing Options
% 3.00/0.99  
% 3.00/0.99  --preprocessing_flag                    true
% 3.00/0.99  --time_out_prep_mult                    0.1
% 3.00/0.99  --splitting_mode                        input
% 3.00/0.99  --splitting_grd                         true
% 3.00/0.99  --splitting_cvd                         false
% 3.00/0.99  --splitting_cvd_svl                     false
% 3.00/0.99  --splitting_nvd                         32
% 3.00/0.99  --sub_typing                            true
% 3.00/0.99  --prep_gs_sim                           true
% 3.00/0.99  --prep_unflatten                        true
% 3.00/0.99  --prep_res_sim                          true
% 3.00/0.99  --prep_upred                            true
% 3.00/0.99  --prep_sem_filter                       exhaustive
% 3.00/0.99  --prep_sem_filter_out                   false
% 3.00/0.99  --pred_elim                             true
% 3.00/0.99  --res_sim_input                         true
% 3.00/0.99  --eq_ax_congr_red                       true
% 3.00/0.99  --pure_diseq_elim                       true
% 3.00/0.99  --brand_transform                       false
% 3.00/0.99  --non_eq_to_eq                          false
% 3.00/0.99  --prep_def_merge                        true
% 3.00/0.99  --prep_def_merge_prop_impl              false
% 3.00/0.99  --prep_def_merge_mbd                    true
% 3.00/0.99  --prep_def_merge_tr_red                 false
% 3.00/0.99  --prep_def_merge_tr_cl                  false
% 3.00/0.99  --smt_preprocessing                     true
% 3.00/0.99  --smt_ac_axioms                         fast
% 3.00/0.99  --preprocessed_out                      false
% 3.00/0.99  --preprocessed_stats                    false
% 3.00/0.99  
% 3.00/0.99  ------ Abstraction refinement Options
% 3.00/0.99  
% 3.00/0.99  --abstr_ref                             []
% 3.00/0.99  --abstr_ref_prep                        false
% 3.00/0.99  --abstr_ref_until_sat                   false
% 3.00/0.99  --abstr_ref_sig_restrict                funpre
% 3.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/0.99  --abstr_ref_under                       []
% 3.00/0.99  
% 3.00/0.99  ------ SAT Options
% 3.00/0.99  
% 3.00/0.99  --sat_mode                              false
% 3.00/0.99  --sat_fm_restart_options                ""
% 3.00/0.99  --sat_gr_def                            false
% 3.00/0.99  --sat_epr_types                         true
% 3.00/0.99  --sat_non_cyclic_types                  false
% 3.00/0.99  --sat_finite_models                     false
% 3.00/0.99  --sat_fm_lemmas                         false
% 3.00/0.99  --sat_fm_prep                           false
% 3.00/0.99  --sat_fm_uc_incr                        true
% 3.00/0.99  --sat_out_model                         small
% 3.00/0.99  --sat_out_clauses                       false
% 3.00/0.99  
% 3.00/0.99  ------ QBF Options
% 3.00/0.99  
% 3.00/0.99  --qbf_mode                              false
% 3.00/0.99  --qbf_elim_univ                         false
% 3.00/0.99  --qbf_dom_inst                          none
% 3.00/0.99  --qbf_dom_pre_inst                      false
% 3.00/0.99  --qbf_sk_in                             false
% 3.00/0.99  --qbf_pred_elim                         true
% 3.00/0.99  --qbf_split                             512
% 3.00/0.99  
% 3.00/0.99  ------ BMC1 Options
% 3.00/0.99  
% 3.00/0.99  --bmc1_incremental                      false
% 3.00/0.99  --bmc1_axioms                           reachable_all
% 3.00/0.99  --bmc1_min_bound                        0
% 3.00/0.99  --bmc1_max_bound                        -1
% 3.00/0.99  --bmc1_max_bound_default                -1
% 3.00/0.99  --bmc1_symbol_reachability              true
% 3.00/0.99  --bmc1_property_lemmas                  false
% 3.00/0.99  --bmc1_k_induction                      false
% 3.00/0.99  --bmc1_non_equiv_states                 false
% 3.00/0.99  --bmc1_deadlock                         false
% 3.00/0.99  --bmc1_ucm                              false
% 3.00/0.99  --bmc1_add_unsat_core                   none
% 3.00/0.99  --bmc1_unsat_core_children              false
% 3.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/0.99  --bmc1_out_stat                         full
% 3.00/0.99  --bmc1_ground_init                      false
% 3.00/0.99  --bmc1_pre_inst_next_state              false
% 3.00/0.99  --bmc1_pre_inst_state                   false
% 3.00/0.99  --bmc1_pre_inst_reach_state             false
% 3.00/0.99  --bmc1_out_unsat_core                   false
% 3.00/0.99  --bmc1_aig_witness_out                  false
% 3.00/0.99  --bmc1_verbose                          false
% 3.00/0.99  --bmc1_dump_clauses_tptp                false
% 3.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.00/0.99  --bmc1_dump_file                        -
% 3.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.00/0.99  --bmc1_ucm_extend_mode                  1
% 3.00/0.99  --bmc1_ucm_init_mode                    2
% 3.00/0.99  --bmc1_ucm_cone_mode                    none
% 3.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.00/0.99  --bmc1_ucm_relax_model                  4
% 3.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/0.99  --bmc1_ucm_layered_model                none
% 3.00/0.99  --bmc1_ucm_max_lemma_size               10
% 3.00/0.99  
% 3.00/0.99  ------ AIG Options
% 3.00/0.99  
% 3.00/0.99  --aig_mode                              false
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation Options
% 3.00/0.99  
% 3.00/0.99  --instantiation_flag                    true
% 3.00/0.99  --inst_sos_flag                         false
% 3.00/0.99  --inst_sos_phase                        true
% 3.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/0.99  --inst_lit_sel_side                     none
% 3.00/0.99  --inst_solver_per_active                1400
% 3.00/0.99  --inst_solver_calls_frac                1.
% 3.00/0.99  --inst_passive_queue_type               priority_queues
% 3.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/0.99  --inst_passive_queues_freq              [25;2]
% 3.00/0.99  --inst_dismatching                      true
% 3.00/0.99  --inst_eager_unprocessed_to_passive     true
% 3.00/0.99  --inst_prop_sim_given                   true
% 3.00/0.99  --inst_prop_sim_new                     false
% 3.00/0.99  --inst_subs_new                         false
% 3.00/0.99  --inst_eq_res_simp                      false
% 3.00/0.99  --inst_subs_given                       false
% 3.00/0.99  --inst_orphan_elimination               true
% 3.00/0.99  --inst_learning_loop_flag               true
% 3.00/0.99  --inst_learning_start                   3000
% 3.00/0.99  --inst_learning_factor                  2
% 3.00/0.99  --inst_start_prop_sim_after_learn       3
% 3.00/0.99  --inst_sel_renew                        solver
% 3.00/0.99  --inst_lit_activity_flag                true
% 3.00/0.99  --inst_restr_to_given                   false
% 3.00/0.99  --inst_activity_threshold               500
% 3.00/0.99  --inst_out_proof                        true
% 3.00/0.99  
% 3.00/0.99  ------ Resolution Options
% 3.00/0.99  
% 3.00/0.99  --resolution_flag                       false
% 3.00/0.99  --res_lit_sel                           adaptive
% 3.00/0.99  --res_lit_sel_side                      none
% 3.00/0.99  --res_ordering                          kbo
% 3.00/0.99  --res_to_prop_solver                    active
% 3.00/0.99  --res_prop_simpl_new                    false
% 3.00/0.99  --res_prop_simpl_given                  true
% 3.00/0.99  --res_passive_queue_type                priority_queues
% 3.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/0.99  --res_passive_queues_freq               [15;5]
% 3.00/0.99  --res_forward_subs                      full
% 3.00/0.99  --res_backward_subs                     full
% 3.00/0.99  --res_forward_subs_resolution           true
% 3.00/0.99  --res_backward_subs_resolution          true
% 3.00/0.99  --res_orphan_elimination                true
% 3.00/0.99  --res_time_limit                        2.
% 3.00/0.99  --res_out_proof                         true
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Options
% 3.00/0.99  
% 3.00/0.99  --superposition_flag                    true
% 3.00/0.99  --sup_passive_queue_type                priority_queues
% 3.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.00/0.99  --demod_completeness_check              fast
% 3.00/0.99  --demod_use_ground                      true
% 3.00/0.99  --sup_to_prop_solver                    passive
% 3.00/0.99  --sup_prop_simpl_new                    true
% 3.00/0.99  --sup_prop_simpl_given                  true
% 3.00/0.99  --sup_fun_splitting                     false
% 3.00/0.99  --sup_smt_interval                      50000
% 3.00/0.99  
% 3.00/0.99  ------ Superposition Simplification Setup
% 3.00/0.99  
% 3.00/0.99  --sup_indices_passive                   []
% 3.00/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_full_bw                           [BwDemod]
% 3.00/0.99  --sup_immed_triv                        [TrivRules]
% 3.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_immed_bw_main                     []
% 3.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/0.99  
% 3.00/0.99  ------ Combination Options
% 3.00/0.99  
% 3.00/0.99  --comb_res_mult                         3
% 3.00/0.99  --comb_sup_mult                         2
% 3.00/0.99  --comb_inst_mult                        10
% 3.00/0.99  
% 3.00/0.99  ------ Debug Options
% 3.00/0.99  
% 3.00/0.99  --dbg_backtrace                         false
% 3.00/0.99  --dbg_dump_prop_clauses                 false
% 3.00/0.99  --dbg_dump_prop_clauses_file            -
% 3.00/0.99  --dbg_out_stat                          false
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  ------ Proving...
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  % SZS output start Saturation for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  fof(f9,axiom,(
% 3.00/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f38,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f9])).
% 3.00/0.99  
% 3.00/0.99  fof(f5,axiom,(
% 3.00/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f34,plain,(
% 3.00/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.00/0.99    inference(cnf_transformation,[],[f5])).
% 3.00/0.99  
% 3.00/0.99  fof(f14,axiom,(
% 3.00/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f43,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f14])).
% 3.00/0.99  
% 3.00/0.99  fof(f54,plain,(
% 3.00/0.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 3.00/0.99    inference(definition_unfolding,[],[f34,f43])).
% 3.00/0.99  
% 3.00/0.99  fof(f2,axiom,(
% 3.00/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f25,plain,(
% 3.00/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.00/0.99    inference(nnf_transformation,[],[f2])).
% 3.00/0.99  
% 3.00/0.99  fof(f31,plain,(
% 3.00/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.00/0.99    inference(cnf_transformation,[],[f25])).
% 3.00/0.99  
% 3.00/0.99  fof(f52,plain,(
% 3.00/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.00/0.99    inference(definition_unfolding,[],[f31,f43])).
% 3.00/0.99  
% 3.00/0.99  fof(f11,axiom,(
% 3.00/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f40,plain,(
% 3.00/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f11])).
% 3.00/0.99  
% 3.00/0.99  fof(f10,axiom,(
% 3.00/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f39,plain,(
% 3.00/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.00/0.99    inference(cnf_transformation,[],[f10])).
% 3.00/0.99  
% 3.00/0.99  fof(f13,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f22,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/0.99    inference(ennf_transformation,[],[f13])).
% 3.00/0.99  
% 3.00/0.99  fof(f42,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f22])).
% 3.00/0.99  
% 3.00/0.99  fof(f4,axiom,(
% 3.00/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f33,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f4])).
% 3.00/0.99  
% 3.00/0.99  fof(f49,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.00/0.99    inference(definition_unfolding,[],[f33,f43])).
% 3.00/0.99  
% 3.00/0.99  fof(f58,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.00/0.99    inference(definition_unfolding,[],[f42,f49])).
% 3.00/0.99  
% 3.00/0.99  fof(f7,axiom,(
% 3.00/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f19,plain,(
% 3.00/0.99    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.00/0.99    inference(ennf_transformation,[],[f7])).
% 3.00/0.99  
% 3.00/0.99  fof(f36,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f19])).
% 3.00/0.99  
% 3.00/0.99  fof(f8,axiom,(
% 3.00/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f37,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f8])).
% 3.00/0.99  
% 3.00/0.99  fof(f50,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 3.00/0.99    inference(definition_unfolding,[],[f37,f49])).
% 3.00/0.99  
% 3.00/0.99  fof(f56,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.99    inference(definition_unfolding,[],[f36,f49,f50])).
% 3.00/0.99  
% 3.00/0.99  fof(f1,axiom,(
% 3.00/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f29,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f1])).
% 3.00/0.99  
% 3.00/0.99  fof(f51,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 3.00/0.99    inference(definition_unfolding,[],[f29,f50,f50])).
% 3.00/0.99  
% 3.00/0.99  fof(f6,axiom,(
% 3.00/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f35,plain,(
% 3.00/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.00/0.99    inference(cnf_transformation,[],[f6])).
% 3.00/0.99  
% 3.00/0.99  fof(f55,plain,(
% 3.00/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 3.00/0.99    inference(definition_unfolding,[],[f35,f49])).
% 3.00/0.99  
% 3.00/0.99  fof(f12,axiom,(
% 3.00/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f20,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.00/0.99    inference(ennf_transformation,[],[f12])).
% 3.00/0.99  
% 3.00/0.99  fof(f21,plain,(
% 3.00/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.00/0.99    inference(flattening,[],[f20])).
% 3.00/0.99  
% 3.00/0.99  fof(f41,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.00/0.99    inference(cnf_transformation,[],[f21])).
% 3.00/0.99  
% 3.00/0.99  fof(f57,plain,(
% 3.00/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.00/0.99    inference(definition_unfolding,[],[f41,f50])).
% 3.00/0.99  
% 3.00/0.99  fof(f15,conjecture,(
% 3.00/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f16,negated_conjecture,(
% 3.00/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 3.00/0.99    inference(negated_conjecture,[],[f15])).
% 3.00/0.99  
% 3.00/0.99  fof(f17,plain,(
% 3.00/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 3.00/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.00/0.99  
% 3.00/0.99  fof(f23,plain,(
% 3.00/0.99    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 3.00/0.99    inference(ennf_transformation,[],[f17])).
% 3.00/0.99  
% 3.00/0.99  fof(f24,plain,(
% 3.00/0.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 3.00/0.99    inference(flattening,[],[f23])).
% 3.00/0.99  
% 3.00/0.99  fof(f27,plain,(
% 3.00/0.99    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f26,plain,(
% 3.00/0.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.00/0.99    introduced(choice_axiom,[])).
% 3.00/0.99  
% 3.00/0.99  fof(f28,plain,(
% 3.00/0.99    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26])).
% 3.00/0.99  
% 3.00/0.99  fof(f44,plain,(
% 3.00/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  fof(f45,plain,(
% 3.00/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  fof(f47,plain,(
% 3.00/0.99    r1_xboole_0(sK1,sK2)),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  fof(f3,axiom,(
% 3.00/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.00/0.99  
% 3.00/0.99  fof(f18,plain,(
% 3.00/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.00/0.99    inference(ennf_transformation,[],[f3])).
% 3.00/0.99  
% 3.00/0.99  fof(f32,plain,(
% 3.00/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f18])).
% 3.00/0.99  
% 3.00/0.99  fof(f30,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.99    inference(cnf_transformation,[],[f25])).
% 3.00/0.99  
% 3.00/0.99  fof(f53,plain,(
% 3.00/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.99    inference(definition_unfolding,[],[f30,f43])).
% 3.00/0.99  
% 3.00/0.99  fof(f46,plain,(
% 3.00/0.99    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  fof(f48,plain,(
% 3.00/0.99    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 3.00/0.99    inference(cnf_transformation,[],[f28])).
% 3.00/0.99  
% 3.00/0.99  cnf(c_136,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_7,plain,
% 3.00/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4,plain,
% 3.00/0.99      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_804,plain,
% 3.00/0.99      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1,plain,
% 3.00/0.99      ( r1_xboole_0(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_461,plain,
% 3.00/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 3.00/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1984,plain,
% 3.00/0.99      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_804,c_461]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_9,plain,
% 3.00/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.00/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_457,plain,
% 3.00/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_8,plain,
% 3.00/0.99      ( k2_subset_1(X0) = X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_472,plain,
% 3.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_457,c_8]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_11,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/0.99      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.00/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_455,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_930,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_472,c_455]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6,plain,
% 3.00/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.00/0.99      | k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) = X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_458,plain,
% 3.00/0.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) = X0
% 3.00/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3528,plain,
% 3.00/0.99      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1))) = X0
% 3.00/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_930,c_458]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3568,plain,
% 3.00/0.99      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1) = X0
% 3.00/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_3528,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6968,plain,
% 3.00/0.99      ( k7_subset_1(k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)),k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)),X0) = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1984,c_3568]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_0,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
% 3.00/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1154,plain,
% 3.00/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_804,c_0]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_479,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_5,c_4]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1157,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_1154,c_4,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1158,plain,
% 3.00/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_1157,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3586,plain,
% 3.00/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3618,plain,
% 3.00/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_3586,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_6970,plain,
% 3.00/0.99      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_6968,c_1158,c_3618]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_10,plain,
% 3.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.00/0.99      | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_456,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
% 3.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1649,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X0,X0,X1)
% 3.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_472,c_456]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5269,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X0,X0,X1)
% 3.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_1649,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5275,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k7_subset_1(X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_472,c_5269]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_7050,plain,
% 3.00/0.99      ( k4_subset_1(X0,X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_6970,c_5275]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_7051,plain,
% 3.00/0.99      ( k4_subset_1(X0,X0,X0) = X0 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_7050,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_16,negated_conjecture,
% 3.00/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.00/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_452,plain,
% 3.00/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_796,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_452,c_455]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1285,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_796,c_0]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1553,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(sK1,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_7,c_1285]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3595,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,sK1)) = k5_xboole_0(sK1,k7_subset_1(sK1,sK1,sK1)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_930,c_1553]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1648,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_452,c_456]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1656,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_1648,c_1285]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2201,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_452,c_1656]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3597,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k7_subset_1(sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_3595,c_2201]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5441,plain,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_5275,c_3597]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_7055,plain,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_7051,c_5441]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_15,negated_conjecture,
% 3.00/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.00/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_453,plain,
% 3.00/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_795,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_453,c_455]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1165,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_795,c_0]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1425,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_7,c_1165]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3594,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK2,sK2)) = k5_xboole_0(sK2,k7_subset_1(sK2,sK2,sK2)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_930,c_1425]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1647,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_453,c_456]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1661,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_1647,c_1165]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2369,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_453,c_1661]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3600,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(sK2,sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_3594,c_2369]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5440,plain,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_5275,c_3600]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_7054,plain,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_7051,c_5440]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5449,plain,
% 3.00/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_5275,c_1158]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3589,plain,
% 3.00/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_804,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3609,plain,
% 3.00/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_3589,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5451,plain,
% 3.00/0.99      ( k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_5449,c_3609]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3529,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X2,X0,X1)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_930,c_456]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5423,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_452,c_3529]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5422,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_453,c_3529]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5273,plain,
% 3.00/0.99      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_453,c_5269]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2371,plain,
% 3.00/0.99      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_472,c_1661]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3533,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_930,c_795]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4944,plain,
% 3.00/0.99      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2371,c_3533]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5282,plain,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_5273,c_4944]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5274,plain,
% 3.00/0.99      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_452,c_5269]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2202,plain,
% 3.00/0.99      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_472,c_1656]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3534,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_930,c_796]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4855,plain,
% 3.00/0.99      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2202,c_3534]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5279,plain,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_5274,c_4855]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3530,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_930,c_0]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3558,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_3530,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5054,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_3558,c_4944]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_5053,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_3558,c_4855]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_13,negated_conjecture,
% 3.00/0.99      ( r1_xboole_0(sK1,sK2) ),
% 3.00/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_454,plain,
% 3.00/0.99      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2479,plain,
% 3.00/0.99      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))),sK2))) = sK1 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_454,c_458]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3,plain,
% 3.00/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_459,plain,
% 3.00/0.99      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1894,plain,
% 3.00/0.99      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_454,c_459]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2,plain,
% 3.00/0.99      ( ~ r1_xboole_0(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 3.00/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_460,plain,
% 3.00/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 3.00/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.00/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2072,plain,
% 3.00/0.99      ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1894,c_460]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2490,plain,
% 3.00/0.99      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)),sK2))) = sK1 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2479,c_2072]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2491,plain,
% 3.00/0.99      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK2),sK2))) = sK1 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2490,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2151,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2072,c_1285]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1423,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_796,c_1165]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2154,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2151,c_479,c_1423]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1899,plain,
% 3.00/0.99      ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_xboole_0 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_454,c_460]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2080,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1899,c_796]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2091,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = sK1 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2080,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2200,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_453,c_1656]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_14,negated_conjecture,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 3.00/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2208,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_struct_0(sK0) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2200,c_14]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3350,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2091,c_2208]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3525,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2154,c_2091,c_3350]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4845,plain,
% 3.00/0.99      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))) = sK1 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2491,c_3525]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4848,plain,
% 3.00/0.99      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) = sK1 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_7,c_4845]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4850,plain,
% 3.00/0.99      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4845,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2481,plain,
% 3.00/0.99      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2)))),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK2)))),sK1))) = sK2 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1894,c_458]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2483,plain,
% 3.00/0.99      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)),sK1))) = sK2 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2481,c_1899]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2484,plain,
% 3.00/0.99      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,sK1),sK1))) = sK2 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2483,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4577,plain,
% 3.00/0.99      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = sK2 ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2484,c_3350]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4580,plain,
% 3.00/0.99      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) = sK2 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_7,c_4577]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_4582,plain,
% 3.00/0.99      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4577,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1282,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4,c_796]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1292,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_1282,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3839,plain,
% 3.00/0.99      ( k7_subset_1(sK1,sK1,k1_xboole_0) = sK1 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_3534,c_1292]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3828,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_3534,c_1656]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1162,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = k5_xboole_0(sK2,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4,c_795]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1172,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = sK2 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_1162,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3823,plain,
% 3.00/0.99      ( k7_subset_1(sK2,sK2,k1_xboole_0) = sK2 ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_3533,c_1172]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3812,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_3533,c_1661]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3587,plain,
% 3.00/0.99      ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1899,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3615,plain,
% 3.00/0.99      ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_3587,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3588,plain,
% 3.00/0.99      ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_2072,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3612,plain,
% 3.00/0.99      ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_3588,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3590,plain,
% 3.00/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_7,c_930]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3532,plain,
% 3.00/0.99      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 3.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_930,c_455]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2370,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_452,c_1661]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2079,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1899,c_0]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2094,plain,
% 3.00/0.99      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2079,c_479,c_795,c_1285]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2375,plain,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,sK1) ),
% 3.00/0.99      inference(light_normalisation,[status(thm)],[c_2370,c_2094]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_3437,plain,
% 3.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_3350,c_2375]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1163,plain,
% 3.00/0.99      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(X0,sK2))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_7,c_795]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2082,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_1899,c_1163]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_2084,plain,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = sK2 ),
% 3.00/0.99      inference(demodulation,[status(thm)],[c_2082,c_479]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1985,plain,
% 3.00/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 3.00/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_7,c_461]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_1983,plain,
% 3.00/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.00/0.99      inference(superposition,[status(thm)],[c_4,c_461]) ).
% 3.00/0.99  
% 3.00/0.99  cnf(c_12,negated_conjecture,
% 3.00/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 3.00/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  % SZS output end Saturation for theBenchmark.p
% 3.00/0.99  
% 3.00/0.99  ------                               Statistics
% 3.00/0.99  
% 3.00/0.99  ------ General
% 3.00/0.99  
% 3.00/0.99  abstr_ref_over_cycles:                  0
% 3.00/0.99  abstr_ref_under_cycles:                 0
% 3.00/0.99  gc_basic_clause_elim:                   0
% 3.00/0.99  forced_gc_time:                         0
% 3.00/0.99  parsing_time:                           0.008
% 3.00/0.99  unif_index_cands_time:                  0.
% 3.00/0.99  unif_index_add_time:                    0.
% 3.00/0.99  orderings_time:                         0.
% 3.00/0.99  out_proof_time:                         0.
% 3.00/0.99  total_time:                             0.273
% 3.00/0.99  num_of_symbols:                         46
% 3.00/0.99  num_of_terms:                           6338
% 3.00/0.99  
% 3.00/0.99  ------ Preprocessing
% 3.00/0.99  
% 3.00/0.99  num_of_splits:                          0
% 3.00/0.99  num_of_split_atoms:                     0
% 3.00/0.99  num_of_reused_defs:                     0
% 3.00/0.99  num_eq_ax_congr_red:                    2
% 3.00/0.99  num_of_sem_filtered_clauses:            1
% 3.00/0.99  num_of_subtypes:                        0
% 3.00/0.99  monotx_restored_types:                  0
% 3.00/0.99  sat_num_of_epr_types:                   0
% 3.00/0.99  sat_num_of_non_cyclic_types:            0
% 3.00/0.99  sat_guarded_non_collapsed_types:        0
% 3.00/0.99  num_pure_diseq_elim:                    0
% 3.00/0.99  simp_replaced_by:                       0
% 3.00/0.99  res_preprocessed:                       76
% 3.00/0.99  prep_upred:                             0
% 3.00/0.99  prep_unflattend:                        0
% 3.00/0.99  smt_new_axioms:                         0
% 3.00/0.99  pred_elim_cands:                        2
% 3.00/0.99  pred_elim:                              0
% 3.00/0.99  pred_elim_cl:                           0
% 3.00/0.99  pred_elim_cycles:                       1
% 3.00/0.99  merged_defs:                            6
% 3.00/0.99  merged_defs_ncl:                        0
% 3.00/0.99  bin_hyper_res:                          6
% 3.00/0.99  prep_cycles:                            3
% 3.00/0.99  pred_elim_time:                         0.
% 3.00/0.99  splitting_time:                         0.
% 3.00/0.99  sem_filter_time:                        0.
% 3.00/0.99  monotx_time:                            0.
% 3.00/0.99  subtype_inf_time:                       0.
% 3.00/0.99  
% 3.00/0.99  ------ Problem properties
% 3.00/0.99  
% 3.00/0.99  clauses:                                17
% 3.00/0.99  conjectures:                            5
% 3.00/0.99  epr:                                    2
% 3.00/0.99  horn:                                   17
% 3.00/0.99  ground:                                 5
% 3.00/0.99  unary:                                  11
% 3.00/0.99  binary:                                 5
% 3.00/0.99  lits:                                   24
% 3.00/0.99  lits_eq:                                12
% 3.00/0.99  fd_pure:                                0
% 3.00/0.99  fd_pseudo:                              0
% 3.00/0.99  fd_cond:                                0
% 3.00/0.99  fd_pseudo_cond:                         0
% 3.00/0.99  ac_symbols:                             0
% 3.00/0.99  
% 3.00/0.99  ------ Propositional Solver
% 3.00/0.99  
% 3.00/0.99  prop_solver_calls:                      24
% 3.00/0.99  prop_fast_solver_calls:                 408
% 3.00/0.99  smt_solver_calls:                       0
% 3.00/0.99  smt_fast_solver_calls:                  0
% 3.00/0.99  prop_num_of_clauses:                    3161
% 3.00/0.99  prop_preprocess_simplified:             7516
% 3.00/0.99  prop_fo_subsumed:                       0
% 3.00/0.99  prop_solver_time:                       0.
% 3.00/0.99  smt_solver_time:                        0.
% 3.00/0.99  smt_fast_solver_time:                   0.
% 3.00/0.99  prop_fast_solver_time:                  0.
% 3.00/0.99  prop_unsat_core_time:                   0.
% 3.00/0.99  
% 3.00/0.99  ------ QBF
% 3.00/0.99  
% 3.00/0.99  qbf_q_res:                              0
% 3.00/0.99  qbf_num_tautologies:                    0
% 3.00/0.99  qbf_prep_cycles:                        0
% 3.00/0.99  
% 3.00/0.99  ------ BMC1
% 3.00/0.99  
% 3.00/0.99  bmc1_current_bound:                     -1
% 3.00/0.99  bmc1_last_solved_bound:                 -1
% 3.00/0.99  bmc1_unsat_core_size:                   -1
% 3.00/0.99  bmc1_unsat_core_parents_size:           -1
% 3.00/0.99  bmc1_merge_next_fun:                    0
% 3.00/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.00/0.99  
% 3.00/0.99  ------ Instantiation
% 3.00/0.99  
% 3.00/0.99  inst_num_of_clauses:                    1154
% 3.00/0.99  inst_num_in_passive:                    591
% 3.00/0.99  inst_num_in_active:                     445
% 3.00/0.99  inst_num_in_unprocessed:                118
% 3.00/0.99  inst_num_of_loops:                      460
% 3.00/0.99  inst_num_of_learning_restarts:          0
% 3.00/0.99  inst_num_moves_active_passive:          14
% 3.00/0.99  inst_lit_activity:                      0
% 3.00/0.99  inst_lit_activity_moves:                0
% 3.00/0.99  inst_num_tautologies:                   0
% 3.00/0.99  inst_num_prop_implied:                  0
% 3.00/0.99  inst_num_existing_simplified:           0
% 3.00/0.99  inst_num_eq_res_simplified:             0
% 3.00/0.99  inst_num_child_elim:                    0
% 3.00/0.99  inst_num_of_dismatching_blockings:      187
% 3.00/0.99  inst_num_of_non_proper_insts:           883
% 3.00/0.99  inst_num_of_duplicates:                 0
% 3.00/0.99  inst_inst_num_from_inst_to_res:         0
% 3.00/0.99  inst_dismatching_checking_time:         0.
% 3.00/0.99  
% 3.00/0.99  ------ Resolution
% 3.00/0.99  
% 3.00/0.99  res_num_of_clauses:                     0
% 3.00/0.99  res_num_in_passive:                     0
% 3.00/0.99  res_num_in_active:                      0
% 3.00/0.99  res_num_of_loops:                       79
% 3.00/0.99  res_forward_subset_subsumed:            56
% 3.00/0.99  res_backward_subset_subsumed:           0
% 3.00/0.99  res_forward_subsumed:                   0
% 3.00/0.99  res_backward_subsumed:                  0
% 3.00/0.99  res_forward_subsumption_resolution:     0
% 3.00/0.99  res_backward_subsumption_resolution:    0
% 3.00/0.99  res_clause_to_clause_subsumption:       216
% 3.00/0.99  res_orphan_elimination:                 0
% 3.00/0.99  res_tautology_del:                      43
% 3.00/0.99  res_num_eq_res_simplified:              0
% 3.00/0.99  res_num_sel_changes:                    0
% 3.00/0.99  res_moves_from_active_to_pass:          0
% 3.00/0.99  
% 3.00/0.99  ------ Superposition
% 3.00/0.99  
% 3.00/0.99  sup_time_total:                         0.
% 3.00/0.99  sup_time_generating:                    0.
% 3.00/0.99  sup_time_sim_full:                      0.
% 3.00/0.99  sup_time_sim_immed:                     0.
% 3.00/0.99  
% 3.00/0.99  sup_num_of_clauses:                     74
% 3.00/0.99  sup_num_in_active:                      64
% 3.00/0.99  sup_num_in_passive:                     10
% 3.00/0.99  sup_num_of_loops:                       90
% 3.00/0.99  sup_fw_superposition:                   158
% 3.00/0.99  sup_bw_superposition:                   56
% 3.00/0.99  sup_immediate_simplified:               58
% 3.00/0.99  sup_given_eliminated:                   0
% 3.00/0.99  comparisons_done:                       0
% 3.00/0.99  comparisons_avoided:                    0
% 3.00/0.99  
% 3.00/0.99  ------ Simplifications
% 3.00/0.99  
% 3.00/0.99  
% 3.00/0.99  sim_fw_subset_subsumed:                 0
% 3.00/0.99  sim_bw_subset_subsumed:                 0
% 3.00/0.99  sim_fw_subsumed:                        5
% 3.00/0.99  sim_bw_subsumed:                        2
% 3.00/0.99  sim_fw_subsumption_res:                 0
% 3.00/0.99  sim_bw_subsumption_res:                 0
% 3.00/0.99  sim_tautology_del:                      0
% 3.00/0.99  sim_eq_tautology_del:                   21
% 3.00/0.99  sim_eq_res_simp:                        0
% 3.00/0.99  sim_fw_demodulated:                     30
% 3.00/0.99  sim_bw_demodulated:                     28
% 3.00/0.99  sim_light_normalised:                   47
% 3.00/0.99  sim_joinable_taut:                      0
% 3.00/0.99  sim_joinable_simp:                      0
% 3.00/0.99  sim_ac_normalised:                      0
% 3.00/0.99  sim_smt_subsumption:                    0
% 3.00/0.99  
%------------------------------------------------------------------------------
