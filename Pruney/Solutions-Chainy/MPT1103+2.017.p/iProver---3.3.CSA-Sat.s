%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:50 EST 2020

% Result     : CounterSatisfiable 1.95s
% Output     : Saturation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 497 expanded)
%              Number of clauses        :   47 ( 158 expanded)
%              Number of leaves         :   16 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 814 expanded)
%              Number of equality atoms :  111 ( 587 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f17,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ( ~ ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
          & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ( k2_struct_0(X0) = X1
          & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
        | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
          & k2_struct_0(X0) != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ( k2_struct_0(X0) = X1
            & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
          | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
            & k2_struct_0(X0) != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ( ( k2_struct_0(sK0) = sK1
          & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
        | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
          & k2_struct_0(sK0) != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
    inference(definition_unfolding,[],[f27,f43,f35,f42])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f38,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_90,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_433,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_106,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_0])).

cnf(c_432,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_106])).

cnf(c_693,plain,
    ( k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_433,c_432])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_435,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_435,c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_434,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1218,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_446,c_434])).

cnf(c_1244,plain,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_693,c_1218])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1261,plain,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1244,c_4])).

cnf(c_5,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1233,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
    inference(demodulation,[status(thm)],[c_1218,c_2])).

cnf(c_1235,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(demodulation,[status(thm)],[c_1233,c_1218])).

cnf(c_1762,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k7_subset_1(k7_subset_1(X1,X1,X0),k7_subset_1(X1,X1,X0),k1_setfam_1(k2_tarski(X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_5,c_1235])).

cnf(c_1917,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)),k7_subset_1(k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))) = sK1 ),
    inference(superposition,[status(thm)],[c_1261,c_1762])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_839,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_845,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_839,c_1,c_3])).

cnf(c_1249,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1218,c_845])).

cnf(c_824,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_1251,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1249,c_824])).

cnf(c_1929,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1917,c_3,c_1251])).

cnf(c_1247,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_1218])).

cnf(c_1406,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_693,c_1247])).

cnf(c_1757,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)),k7_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1406,c_1235])).

cnf(c_1789,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))),k7_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_5,c_1757])).

cnf(c_1793,plain,
    ( k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1),sK1)) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1789,c_693])).

cnf(c_1243,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_1218])).

cnf(c_1264,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1243,c_3])).

cnf(c_970,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_446,c_432])).

cnf(c_1246,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_970,c_1218])).

cnf(c_1256,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1246,c_4])).

cnf(c_1217,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_433,c_434])).

cnf(c_1238,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1217,c_1218])).

cnf(c_1220,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1218,c_434])).

cnf(c_13,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_10,negated_conjecture,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:52:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.95/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.02  
% 1.95/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.95/1.02  
% 1.95/1.02  ------  iProver source info
% 1.95/1.02  
% 1.95/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.95/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.95/1.02  git: non_committed_changes: false
% 1.95/1.02  git: last_make_outside_of_git: false
% 1.95/1.02  
% 1.95/1.02  ------ 
% 1.95/1.02  
% 1.95/1.02  ------ Input Options
% 1.95/1.02  
% 1.95/1.02  --out_options                           all
% 1.95/1.02  --tptp_safe_out                         true
% 1.95/1.02  --problem_path                          ""
% 1.95/1.02  --include_path                          ""
% 1.95/1.02  --clausifier                            res/vclausify_rel
% 1.95/1.02  --clausifier_options                    --mode clausify
% 1.95/1.02  --stdin                                 false
% 1.95/1.02  --stats_out                             all
% 1.95/1.02  
% 1.95/1.02  ------ General Options
% 1.95/1.02  
% 1.95/1.02  --fof                                   false
% 1.95/1.02  --time_out_real                         305.
% 1.95/1.02  --time_out_virtual                      -1.
% 1.95/1.02  --symbol_type_check                     false
% 1.95/1.02  --clausify_out                          false
% 1.95/1.02  --sig_cnt_out                           false
% 1.95/1.02  --trig_cnt_out                          false
% 1.95/1.02  --trig_cnt_out_tolerance                1.
% 1.95/1.02  --trig_cnt_out_sk_spl                   false
% 1.95/1.02  --abstr_cl_out                          false
% 1.95/1.02  
% 1.95/1.02  ------ Global Options
% 1.95/1.02  
% 1.95/1.02  --schedule                              default
% 1.95/1.02  --add_important_lit                     false
% 1.95/1.02  --prop_solver_per_cl                    1000
% 1.95/1.02  --min_unsat_core                        false
% 1.95/1.02  --soft_assumptions                      false
% 1.95/1.02  --soft_lemma_size                       3
% 1.95/1.02  --prop_impl_unit_size                   0
% 1.95/1.02  --prop_impl_unit                        []
% 1.95/1.02  --share_sel_clauses                     true
% 1.95/1.02  --reset_solvers                         false
% 1.95/1.02  --bc_imp_inh                            [conj_cone]
% 1.95/1.02  --conj_cone_tolerance                   3.
% 1.95/1.02  --extra_neg_conj                        none
% 1.95/1.02  --large_theory_mode                     true
% 1.95/1.02  --prolific_symb_bound                   200
% 1.95/1.02  --lt_threshold                          2000
% 1.95/1.02  --clause_weak_htbl                      true
% 1.95/1.02  --gc_record_bc_elim                     false
% 1.95/1.02  
% 1.95/1.02  ------ Preprocessing Options
% 1.95/1.02  
% 1.95/1.02  --preprocessing_flag                    true
% 1.95/1.02  --time_out_prep_mult                    0.1
% 1.95/1.02  --splitting_mode                        input
% 1.95/1.02  --splitting_grd                         true
% 1.95/1.02  --splitting_cvd                         false
% 1.95/1.02  --splitting_cvd_svl                     false
% 1.95/1.02  --splitting_nvd                         32
% 1.95/1.02  --sub_typing                            true
% 1.95/1.02  --prep_gs_sim                           true
% 1.95/1.02  --prep_unflatten                        true
% 1.95/1.02  --prep_res_sim                          true
% 1.95/1.02  --prep_upred                            true
% 1.95/1.02  --prep_sem_filter                       exhaustive
% 1.95/1.02  --prep_sem_filter_out                   false
% 1.95/1.02  --pred_elim                             true
% 1.95/1.02  --res_sim_input                         true
% 1.95/1.02  --eq_ax_congr_red                       true
% 1.95/1.02  --pure_diseq_elim                       true
% 1.95/1.02  --brand_transform                       false
% 1.95/1.02  --non_eq_to_eq                          false
% 1.95/1.02  --prep_def_merge                        true
% 1.95/1.02  --prep_def_merge_prop_impl              false
% 1.95/1.02  --prep_def_merge_mbd                    true
% 1.95/1.02  --prep_def_merge_tr_red                 false
% 1.95/1.02  --prep_def_merge_tr_cl                  false
% 1.95/1.02  --smt_preprocessing                     true
% 1.95/1.02  --smt_ac_axioms                         fast
% 1.95/1.02  --preprocessed_out                      false
% 1.95/1.02  --preprocessed_stats                    false
% 1.95/1.02  
% 1.95/1.02  ------ Abstraction refinement Options
% 1.95/1.02  
% 1.95/1.02  --abstr_ref                             []
% 1.95/1.02  --abstr_ref_prep                        false
% 1.95/1.02  --abstr_ref_until_sat                   false
% 1.95/1.02  --abstr_ref_sig_restrict                funpre
% 1.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/1.02  --abstr_ref_under                       []
% 1.95/1.02  
% 1.95/1.02  ------ SAT Options
% 1.95/1.02  
% 1.95/1.02  --sat_mode                              false
% 1.95/1.02  --sat_fm_restart_options                ""
% 1.95/1.02  --sat_gr_def                            false
% 1.95/1.02  --sat_epr_types                         true
% 1.95/1.02  --sat_non_cyclic_types                  false
% 1.95/1.02  --sat_finite_models                     false
% 1.95/1.02  --sat_fm_lemmas                         false
% 1.95/1.02  --sat_fm_prep                           false
% 1.95/1.02  --sat_fm_uc_incr                        true
% 1.95/1.02  --sat_out_model                         small
% 1.95/1.02  --sat_out_clauses                       false
% 1.95/1.02  
% 1.95/1.02  ------ QBF Options
% 1.95/1.02  
% 1.95/1.02  --qbf_mode                              false
% 1.95/1.02  --qbf_elim_univ                         false
% 1.95/1.02  --qbf_dom_inst                          none
% 1.95/1.02  --qbf_dom_pre_inst                      false
% 1.95/1.02  --qbf_sk_in                             false
% 1.95/1.02  --qbf_pred_elim                         true
% 1.95/1.02  --qbf_split                             512
% 1.95/1.02  
% 1.95/1.02  ------ BMC1 Options
% 1.95/1.02  
% 1.95/1.02  --bmc1_incremental                      false
% 1.95/1.02  --bmc1_axioms                           reachable_all
% 1.95/1.02  --bmc1_min_bound                        0
% 1.95/1.02  --bmc1_max_bound                        -1
% 1.95/1.02  --bmc1_max_bound_default                -1
% 1.95/1.02  --bmc1_symbol_reachability              true
% 1.95/1.02  --bmc1_property_lemmas                  false
% 1.95/1.02  --bmc1_k_induction                      false
% 1.95/1.02  --bmc1_non_equiv_states                 false
% 1.95/1.02  --bmc1_deadlock                         false
% 1.95/1.02  --bmc1_ucm                              false
% 1.95/1.02  --bmc1_add_unsat_core                   none
% 1.95/1.02  --bmc1_unsat_core_children              false
% 1.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/1.02  --bmc1_out_stat                         full
% 1.95/1.02  --bmc1_ground_init                      false
% 1.95/1.02  --bmc1_pre_inst_next_state              false
% 1.95/1.02  --bmc1_pre_inst_state                   false
% 1.95/1.02  --bmc1_pre_inst_reach_state             false
% 1.95/1.02  --bmc1_out_unsat_core                   false
% 1.95/1.02  --bmc1_aig_witness_out                  false
% 1.95/1.02  --bmc1_verbose                          false
% 1.95/1.02  --bmc1_dump_clauses_tptp                false
% 1.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.95/1.02  --bmc1_dump_file                        -
% 1.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.95/1.02  --bmc1_ucm_extend_mode                  1
% 1.95/1.02  --bmc1_ucm_init_mode                    2
% 1.95/1.02  --bmc1_ucm_cone_mode                    none
% 1.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.95/1.02  --bmc1_ucm_relax_model                  4
% 1.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/1.02  --bmc1_ucm_layered_model                none
% 1.95/1.02  --bmc1_ucm_max_lemma_size               10
% 1.95/1.02  
% 1.95/1.02  ------ AIG Options
% 1.95/1.02  
% 1.95/1.02  --aig_mode                              false
% 1.95/1.02  
% 1.95/1.02  ------ Instantiation Options
% 1.95/1.02  
% 1.95/1.02  --instantiation_flag                    true
% 1.95/1.02  --inst_sos_flag                         false
% 1.95/1.02  --inst_sos_phase                        true
% 1.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/1.02  --inst_lit_sel_side                     num_symb
% 1.95/1.02  --inst_solver_per_active                1400
% 1.95/1.02  --inst_solver_calls_frac                1.
% 1.95/1.02  --inst_passive_queue_type               priority_queues
% 1.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/1.02  --inst_passive_queues_freq              [25;2]
% 1.95/1.02  --inst_dismatching                      true
% 1.95/1.02  --inst_eager_unprocessed_to_passive     true
% 1.95/1.02  --inst_prop_sim_given                   true
% 1.95/1.02  --inst_prop_sim_new                     false
% 1.95/1.02  --inst_subs_new                         false
% 1.95/1.02  --inst_eq_res_simp                      false
% 1.95/1.02  --inst_subs_given                       false
% 1.95/1.02  --inst_orphan_elimination               true
% 1.95/1.02  --inst_learning_loop_flag               true
% 1.95/1.02  --inst_learning_start                   3000
% 1.95/1.02  --inst_learning_factor                  2
% 1.95/1.02  --inst_start_prop_sim_after_learn       3
% 1.95/1.02  --inst_sel_renew                        solver
% 1.95/1.02  --inst_lit_activity_flag                true
% 1.95/1.02  --inst_restr_to_given                   false
% 1.95/1.02  --inst_activity_threshold               500
% 1.95/1.02  --inst_out_proof                        true
% 1.95/1.02  
% 1.95/1.02  ------ Resolution Options
% 1.95/1.02  
% 1.95/1.02  --resolution_flag                       true
% 1.95/1.02  --res_lit_sel                           adaptive
% 1.95/1.02  --res_lit_sel_side                      none
% 1.95/1.02  --res_ordering                          kbo
% 1.95/1.02  --res_to_prop_solver                    active
% 1.95/1.02  --res_prop_simpl_new                    false
% 1.95/1.02  --res_prop_simpl_given                  true
% 1.95/1.02  --res_passive_queue_type                priority_queues
% 1.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/1.02  --res_passive_queues_freq               [15;5]
% 1.95/1.02  --res_forward_subs                      full
% 1.95/1.02  --res_backward_subs                     full
% 1.95/1.02  --res_forward_subs_resolution           true
% 1.95/1.02  --res_backward_subs_resolution          true
% 1.95/1.02  --res_orphan_elimination                true
% 1.95/1.02  --res_time_limit                        2.
% 1.95/1.02  --res_out_proof                         true
% 1.95/1.02  
% 1.95/1.02  ------ Superposition Options
% 1.95/1.02  
% 1.95/1.02  --superposition_flag                    true
% 1.95/1.02  --sup_passive_queue_type                priority_queues
% 1.95/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.95/1.02  --demod_completeness_check              fast
% 1.95/1.02  --demod_use_ground                      true
% 1.95/1.02  --sup_to_prop_solver                    passive
% 1.95/1.02  --sup_prop_simpl_new                    true
% 1.95/1.02  --sup_prop_simpl_given                  true
% 1.95/1.02  --sup_fun_splitting                     false
% 1.95/1.02  --sup_smt_interval                      50000
% 1.95/1.02  
% 1.95/1.02  ------ Superposition Simplification Setup
% 1.95/1.02  
% 1.95/1.02  --sup_indices_passive                   []
% 1.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.02  --sup_full_bw                           [BwDemod]
% 1.95/1.02  --sup_immed_triv                        [TrivRules]
% 1.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.02  --sup_immed_bw_main                     []
% 1.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.02  
% 1.95/1.02  ------ Combination Options
% 1.95/1.02  
% 1.95/1.02  --comb_res_mult                         3
% 1.95/1.02  --comb_sup_mult                         2
% 1.95/1.02  --comb_inst_mult                        10
% 1.95/1.02  
% 1.95/1.02  ------ Debug Options
% 1.95/1.02  
% 1.95/1.02  --dbg_backtrace                         false
% 1.95/1.02  --dbg_dump_prop_clauses                 false
% 1.95/1.02  --dbg_dump_prop_clauses_file            -
% 1.95/1.02  --dbg_out_stat                          false
% 1.95/1.02  ------ Parsing...
% 1.95/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.95/1.02  
% 1.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.95/1.02  
% 1.95/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.95/1.02  
% 1.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.95/1.02  ------ Proving...
% 1.95/1.02  ------ Problem Properties 
% 1.95/1.02  
% 1.95/1.02  
% 1.95/1.02  clauses                                 12
% 1.95/1.02  conjectures                             3
% 1.95/1.02  EPR                                     0
% 1.95/1.02  Horn                                    11
% 1.95/1.02  unary                                   8
% 1.95/1.02  binary                                  4
% 1.95/1.02  lits                                    16
% 1.95/1.02  lits eq                                 12
% 1.95/1.02  fd_pure                                 0
% 1.95/1.02  fd_pseudo                               0
% 1.95/1.02  fd_cond                                 0
% 1.95/1.02  fd_pseudo_cond                          0
% 1.95/1.02  AC symbols                              0
% 1.95/1.02  
% 1.95/1.02  ------ Schedule dynamic 5 is on 
% 1.95/1.02  
% 1.95/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.95/1.02  
% 1.95/1.02  
% 1.95/1.02  ------ 
% 1.95/1.02  Current options:
% 1.95/1.02  ------ 
% 1.95/1.02  
% 1.95/1.02  ------ Input Options
% 1.95/1.02  
% 1.95/1.02  --out_options                           all
% 1.95/1.02  --tptp_safe_out                         true
% 1.95/1.02  --problem_path                          ""
% 1.95/1.02  --include_path                          ""
% 1.95/1.02  --clausifier                            res/vclausify_rel
% 1.95/1.02  --clausifier_options                    --mode clausify
% 1.95/1.02  --stdin                                 false
% 1.95/1.02  --stats_out                             all
% 1.95/1.02  
% 1.95/1.02  ------ General Options
% 1.95/1.02  
% 1.95/1.02  --fof                                   false
% 1.95/1.02  --time_out_real                         305.
% 1.95/1.02  --time_out_virtual                      -1.
% 1.95/1.02  --symbol_type_check                     false
% 1.95/1.02  --clausify_out                          false
% 1.95/1.02  --sig_cnt_out                           false
% 1.95/1.02  --trig_cnt_out                          false
% 1.95/1.02  --trig_cnt_out_tolerance                1.
% 1.95/1.02  --trig_cnt_out_sk_spl                   false
% 1.95/1.02  --abstr_cl_out                          false
% 1.95/1.02  
% 1.95/1.02  ------ Global Options
% 1.95/1.02  
% 1.95/1.02  --schedule                              default
% 1.95/1.02  --add_important_lit                     false
% 1.95/1.02  --prop_solver_per_cl                    1000
% 1.95/1.02  --min_unsat_core                        false
% 1.95/1.02  --soft_assumptions                      false
% 1.95/1.02  --soft_lemma_size                       3
% 1.95/1.02  --prop_impl_unit_size                   0
% 1.95/1.02  --prop_impl_unit                        []
% 1.95/1.02  --share_sel_clauses                     true
% 1.95/1.02  --reset_solvers                         false
% 1.95/1.02  --bc_imp_inh                            [conj_cone]
% 1.95/1.02  --conj_cone_tolerance                   3.
% 1.95/1.02  --extra_neg_conj                        none
% 1.95/1.02  --large_theory_mode                     true
% 1.95/1.02  --prolific_symb_bound                   200
% 1.95/1.02  --lt_threshold                          2000
% 1.95/1.02  --clause_weak_htbl                      true
% 1.95/1.02  --gc_record_bc_elim                     false
% 1.95/1.02  
% 1.95/1.02  ------ Preprocessing Options
% 1.95/1.02  
% 1.95/1.02  --preprocessing_flag                    true
% 1.95/1.02  --time_out_prep_mult                    0.1
% 1.95/1.02  --splitting_mode                        input
% 1.95/1.02  --splitting_grd                         true
% 1.95/1.02  --splitting_cvd                         false
% 1.95/1.02  --splitting_cvd_svl                     false
% 1.95/1.02  --splitting_nvd                         32
% 1.95/1.02  --sub_typing                            true
% 1.95/1.02  --prep_gs_sim                           true
% 1.95/1.02  --prep_unflatten                        true
% 1.95/1.02  --prep_res_sim                          true
% 1.95/1.02  --prep_upred                            true
% 1.95/1.02  --prep_sem_filter                       exhaustive
% 1.95/1.02  --prep_sem_filter_out                   false
% 1.95/1.02  --pred_elim                             true
% 1.95/1.02  --res_sim_input                         true
% 1.95/1.02  --eq_ax_congr_red                       true
% 1.95/1.02  --pure_diseq_elim                       true
% 1.95/1.02  --brand_transform                       false
% 1.95/1.02  --non_eq_to_eq                          false
% 1.95/1.02  --prep_def_merge                        true
% 1.95/1.02  --prep_def_merge_prop_impl              false
% 1.95/1.02  --prep_def_merge_mbd                    true
% 1.95/1.02  --prep_def_merge_tr_red                 false
% 1.95/1.02  --prep_def_merge_tr_cl                  false
% 1.95/1.02  --smt_preprocessing                     true
% 1.95/1.02  --smt_ac_axioms                         fast
% 1.95/1.02  --preprocessed_out                      false
% 1.95/1.02  --preprocessed_stats                    false
% 1.95/1.02  
% 1.95/1.02  ------ Abstraction refinement Options
% 1.95/1.02  
% 1.95/1.02  --abstr_ref                             []
% 1.95/1.02  --abstr_ref_prep                        false
% 1.95/1.02  --abstr_ref_until_sat                   false
% 1.95/1.02  --abstr_ref_sig_restrict                funpre
% 1.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.95/1.02  --abstr_ref_under                       []
% 1.95/1.02  
% 1.95/1.02  ------ SAT Options
% 1.95/1.02  
% 1.95/1.02  --sat_mode                              false
% 1.95/1.02  --sat_fm_restart_options                ""
% 1.95/1.02  --sat_gr_def                            false
% 1.95/1.02  --sat_epr_types                         true
% 1.95/1.02  --sat_non_cyclic_types                  false
% 1.95/1.02  --sat_finite_models                     false
% 1.95/1.02  --sat_fm_lemmas                         false
% 1.95/1.02  --sat_fm_prep                           false
% 1.95/1.02  --sat_fm_uc_incr                        true
% 1.95/1.02  --sat_out_model                         small
% 1.95/1.02  --sat_out_clauses                       false
% 1.95/1.02  
% 1.95/1.02  ------ QBF Options
% 1.95/1.02  
% 1.95/1.02  --qbf_mode                              false
% 1.95/1.02  --qbf_elim_univ                         false
% 1.95/1.02  --qbf_dom_inst                          none
% 1.95/1.02  --qbf_dom_pre_inst                      false
% 1.95/1.02  --qbf_sk_in                             false
% 1.95/1.02  --qbf_pred_elim                         true
% 1.95/1.02  --qbf_split                             512
% 1.95/1.02  
% 1.95/1.02  ------ BMC1 Options
% 1.95/1.02  
% 1.95/1.02  --bmc1_incremental                      false
% 1.95/1.02  --bmc1_axioms                           reachable_all
% 1.95/1.02  --bmc1_min_bound                        0
% 1.95/1.02  --bmc1_max_bound                        -1
% 1.95/1.02  --bmc1_max_bound_default                -1
% 1.95/1.02  --bmc1_symbol_reachability              true
% 1.95/1.02  --bmc1_property_lemmas                  false
% 1.95/1.02  --bmc1_k_induction                      false
% 1.95/1.02  --bmc1_non_equiv_states                 false
% 1.95/1.02  --bmc1_deadlock                         false
% 1.95/1.02  --bmc1_ucm                              false
% 1.95/1.02  --bmc1_add_unsat_core                   none
% 1.95/1.02  --bmc1_unsat_core_children              false
% 1.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.95/1.02  --bmc1_out_stat                         full
% 1.95/1.02  --bmc1_ground_init                      false
% 1.95/1.02  --bmc1_pre_inst_next_state              false
% 1.95/1.02  --bmc1_pre_inst_state                   false
% 1.95/1.02  --bmc1_pre_inst_reach_state             false
% 1.95/1.02  --bmc1_out_unsat_core                   false
% 1.95/1.02  --bmc1_aig_witness_out                  false
% 1.95/1.02  --bmc1_verbose                          false
% 1.95/1.02  --bmc1_dump_clauses_tptp                false
% 1.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.95/1.02  --bmc1_dump_file                        -
% 1.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.95/1.02  --bmc1_ucm_extend_mode                  1
% 1.95/1.03  --bmc1_ucm_init_mode                    2
% 1.95/1.03  --bmc1_ucm_cone_mode                    none
% 1.95/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.95/1.03  --bmc1_ucm_relax_model                  4
% 1.95/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.95/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.95/1.03  --bmc1_ucm_layered_model                none
% 1.95/1.03  --bmc1_ucm_max_lemma_size               10
% 1.95/1.03  
% 1.95/1.03  ------ AIG Options
% 1.95/1.03  
% 1.95/1.03  --aig_mode                              false
% 1.95/1.03  
% 1.95/1.03  ------ Instantiation Options
% 1.95/1.03  
% 1.95/1.03  --instantiation_flag                    true
% 1.95/1.03  --inst_sos_flag                         false
% 1.95/1.03  --inst_sos_phase                        true
% 1.95/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.95/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.95/1.03  --inst_lit_sel_side                     none
% 1.95/1.03  --inst_solver_per_active                1400
% 1.95/1.03  --inst_solver_calls_frac                1.
% 1.95/1.03  --inst_passive_queue_type               priority_queues
% 1.95/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.95/1.03  --inst_passive_queues_freq              [25;2]
% 1.95/1.03  --inst_dismatching                      true
% 1.95/1.03  --inst_eager_unprocessed_to_passive     true
% 1.95/1.03  --inst_prop_sim_given                   true
% 1.95/1.03  --inst_prop_sim_new                     false
% 1.95/1.03  --inst_subs_new                         false
% 1.95/1.03  --inst_eq_res_simp                      false
% 1.95/1.03  --inst_subs_given                       false
% 1.95/1.03  --inst_orphan_elimination               true
% 1.95/1.03  --inst_learning_loop_flag               true
% 1.95/1.03  --inst_learning_start                   3000
% 1.95/1.03  --inst_learning_factor                  2
% 1.95/1.03  --inst_start_prop_sim_after_learn       3
% 1.95/1.03  --inst_sel_renew                        solver
% 1.95/1.03  --inst_lit_activity_flag                true
% 1.95/1.03  --inst_restr_to_given                   false
% 1.95/1.03  --inst_activity_threshold               500
% 1.95/1.03  --inst_out_proof                        true
% 1.95/1.03  
% 1.95/1.03  ------ Resolution Options
% 1.95/1.03  
% 1.95/1.03  --resolution_flag                       false
% 1.95/1.03  --res_lit_sel                           adaptive
% 1.95/1.03  --res_lit_sel_side                      none
% 1.95/1.03  --res_ordering                          kbo
% 1.95/1.03  --res_to_prop_solver                    active
% 1.95/1.03  --res_prop_simpl_new                    false
% 1.95/1.03  --res_prop_simpl_given                  true
% 1.95/1.03  --res_passive_queue_type                priority_queues
% 1.95/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.95/1.03  --res_passive_queues_freq               [15;5]
% 1.95/1.03  --res_forward_subs                      full
% 1.95/1.03  --res_backward_subs                     full
% 1.95/1.03  --res_forward_subs_resolution           true
% 1.95/1.03  --res_backward_subs_resolution          true
% 1.95/1.03  --res_orphan_elimination                true
% 1.95/1.03  --res_time_limit                        2.
% 1.95/1.03  --res_out_proof                         true
% 1.95/1.03  
% 1.95/1.03  ------ Superposition Options
% 1.95/1.03  
% 1.95/1.03  --superposition_flag                    true
% 1.95/1.03  --sup_passive_queue_type                priority_queues
% 1.95/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.95/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.95/1.03  --demod_completeness_check              fast
% 1.95/1.03  --demod_use_ground                      true
% 1.95/1.03  --sup_to_prop_solver                    passive
% 1.95/1.03  --sup_prop_simpl_new                    true
% 1.95/1.03  --sup_prop_simpl_given                  true
% 1.95/1.03  --sup_fun_splitting                     false
% 1.95/1.03  --sup_smt_interval                      50000
% 1.95/1.03  
% 1.95/1.03  ------ Superposition Simplification Setup
% 1.95/1.03  
% 1.95/1.03  --sup_indices_passive                   []
% 1.95/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.95/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.95/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.03  --sup_full_bw                           [BwDemod]
% 1.95/1.03  --sup_immed_triv                        [TrivRules]
% 1.95/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.95/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.03  --sup_immed_bw_main                     []
% 1.95/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.95/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.95/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.95/1.03  
% 1.95/1.03  ------ Combination Options
% 1.95/1.03  
% 1.95/1.03  --comb_res_mult                         3
% 1.95/1.03  --comb_sup_mult                         2
% 1.95/1.03  --comb_inst_mult                        10
% 1.95/1.03  
% 1.95/1.03  ------ Debug Options
% 1.95/1.03  
% 1.95/1.03  --dbg_backtrace                         false
% 1.95/1.03  --dbg_dump_prop_clauses                 false
% 1.95/1.03  --dbg_dump_prop_clauses_file            -
% 1.95/1.03  --dbg_out_stat                          false
% 1.95/1.03  
% 1.95/1.03  
% 1.95/1.03  
% 1.95/1.03  
% 1.95/1.03  ------ Proving...
% 1.95/1.03  
% 1.95/1.03  
% 1.95/1.03  % SZS status CounterSatisfiable for theBenchmark.p
% 1.95/1.03  
% 1.95/1.03  % SZS output start Saturation for theBenchmark.p
% 1.95/1.03  
% 1.95/1.03  fof(f14,conjecture,(
% 1.95/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f15,negated_conjecture,(
% 1.95/1.03    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 1.95/1.03    inference(negated_conjecture,[],[f14])).
% 1.95/1.03  
% 1.95/1.03  fof(f17,plain,(
% 1.95/1.03    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)))),
% 1.95/1.03    inference(pure_predicate_removal,[],[f15])).
% 1.95/1.03  
% 1.95/1.03  fof(f21,plain,(
% 1.95/1.03    ? [X0,X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 1.95/1.03    inference(ennf_transformation,[],[f17])).
% 1.95/1.03  
% 1.95/1.03  fof(f22,plain,(
% 1.95/1.03    ? [X0,X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.95/1.03    introduced(choice_axiom,[])).
% 1.95/1.03  
% 1.95/1.03  fof(f23,plain,(
% 1.95/1.03    ((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.95/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.95/1.03  
% 1.95/1.03  fof(f37,plain,(
% 1.95/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.95/1.03    inference(cnf_transformation,[],[f23])).
% 1.95/1.03  
% 1.95/1.03  fof(f13,axiom,(
% 1.95/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f16,plain,(
% 1.95/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.95/1.03    inference(unused_predicate_definition_removal,[],[f13])).
% 1.95/1.03  
% 1.95/1.03  fof(f20,plain,(
% 1.95/1.03    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.95/1.03    inference(ennf_transformation,[],[f16])).
% 1.95/1.03  
% 1.95/1.03  fof(f36,plain,(
% 1.95/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.95/1.03    inference(cnf_transformation,[],[f20])).
% 1.95/1.03  
% 1.95/1.03  fof(f2,axiom,(
% 1.95/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f18,plain,(
% 1.95/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.95/1.03    inference(ennf_transformation,[],[f2])).
% 1.95/1.03  
% 1.95/1.03  fof(f25,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.95/1.03    inference(cnf_transformation,[],[f18])).
% 1.95/1.03  
% 1.95/1.03  fof(f12,axiom,(
% 1.95/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f35,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.95/1.03    inference(cnf_transformation,[],[f12])).
% 1.95/1.03  
% 1.95/1.03  fof(f44,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.95/1.03    inference(definition_unfolding,[],[f25,f35])).
% 1.95/1.03  
% 1.95/1.03  fof(f10,axiom,(
% 1.95/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f33,plain,(
% 1.95/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.95/1.03    inference(cnf_transformation,[],[f10])).
% 1.95/1.03  
% 1.95/1.03  fof(f9,axiom,(
% 1.95/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f32,plain,(
% 1.95/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.95/1.03    inference(cnf_transformation,[],[f9])).
% 1.95/1.03  
% 1.95/1.03  fof(f11,axiom,(
% 1.95/1.03    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f19,plain,(
% 1.95/1.03    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.95/1.03    inference(ennf_transformation,[],[f11])).
% 1.95/1.03  
% 1.95/1.03  fof(f34,plain,(
% 1.95/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.95/1.03    inference(cnf_transformation,[],[f19])).
% 1.95/1.03  
% 1.95/1.03  fof(f1,axiom,(
% 1.95/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f24,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.95/1.03    inference(cnf_transformation,[],[f1])).
% 1.95/1.03  
% 1.95/1.03  fof(f42,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.95/1.03    inference(definition_unfolding,[],[f24,f35])).
% 1.95/1.03  
% 1.95/1.03  fof(f47,plain,(
% 1.95/1.03    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.95/1.03    inference(definition_unfolding,[],[f34,f42])).
% 1.95/1.03  
% 1.95/1.03  fof(f6,axiom,(
% 1.95/1.03    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f29,plain,(
% 1.95/1.03    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.95/1.03    inference(cnf_transformation,[],[f6])).
% 1.95/1.03  
% 1.95/1.03  fof(f8,axiom,(
% 1.95/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f31,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.95/1.03    inference(cnf_transformation,[],[f8])).
% 1.95/1.03  
% 1.95/1.03  fof(f4,axiom,(
% 1.95/1.03    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f27,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.95/1.03    inference(cnf_transformation,[],[f4])).
% 1.95/1.03  
% 1.95/1.03  fof(f7,axiom,(
% 1.95/1.03    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f30,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.95/1.03    inference(cnf_transformation,[],[f7])).
% 1.95/1.03  
% 1.95/1.03  fof(f43,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 1.95/1.03    inference(definition_unfolding,[],[f30,f42])).
% 1.95/1.03  
% 1.95/1.03  fof(f46,plain,(
% 1.95/1.03    ( ! [X0,X1] : (k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X1)))))) = X0) )),
% 1.95/1.03    inference(definition_unfolding,[],[f27,f43,f35,f42])).
% 1.95/1.03  
% 1.95/1.03  fof(f5,axiom,(
% 1.95/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f28,plain,(
% 1.95/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.95/1.03    inference(cnf_transformation,[],[f5])).
% 1.95/1.03  
% 1.95/1.03  fof(f3,axiom,(
% 1.95/1.03    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.95/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.95/1.03  
% 1.95/1.03  fof(f26,plain,(
% 1.95/1.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.95/1.03    inference(cnf_transformation,[],[f3])).
% 1.95/1.03  
% 1.95/1.03  fof(f45,plain,(
% 1.95/1.03    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.95/1.03    inference(definition_unfolding,[],[f26,f35])).
% 1.95/1.03  
% 1.95/1.03  fof(f38,plain,(
% 1.95/1.03    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1),
% 1.95/1.03    inference(cnf_transformation,[],[f23])).
% 1.95/1.03  
% 1.95/1.03  fof(f41,plain,(
% 1.95/1.03    k2_struct_0(sK0) = sK1 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 1.95/1.03    inference(cnf_transformation,[],[f23])).
% 1.95/1.03  
% 1.95/1.03  cnf(c_90,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_14,negated_conjecture,
% 1.95/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.95/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_433,plain,
% 1.95/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.95/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_9,plain,
% 1.95/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.95/1.03      inference(cnf_transformation,[],[f36]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_0,plain,
% 1.95/1.03      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 1.95/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_106,plain,
% 1.95/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.95/1.03      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 1.95/1.03      inference(resolution,[status(thm)],[c_9,c_0]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_432,plain,
% 1.95/1.03      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 1.95/1.03      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 1.95/1.03      inference(predicate_to_equality,[status(thm)],[c_106]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_693,plain,
% 1.95/1.03      ( k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = sK1 ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_433,c_432]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_7,plain,
% 1.95/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.95/1.03      inference(cnf_transformation,[],[f33]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_435,plain,
% 1.95/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.95/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_6,plain,
% 1.95/1.03      ( k2_subset_1(X0) = X0 ),
% 1.95/1.03      inference(cnf_transformation,[],[f32]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_446,plain,
% 1.95/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.95/1.03      inference(light_normalisation,[status(thm)],[c_435,c_6]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_8,plain,
% 1.95/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.95/1.03      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 1.95/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_434,plain,
% 1.95/1.03      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 1.95/1.03      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 1.95/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1218,plain,
% 1.95/1.03      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_446,c_434]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1244,plain,
% 1.95/1.03      ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_693,c_1218]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_4,plain,
% 1.95/1.03      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.95/1.03      inference(cnf_transformation,[],[f29]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1261,plain,
% 1.95/1.03      ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 1.95/1.03      inference(demodulation,[status(thm)],[c_1244,c_4]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_5,plain,
% 1.95/1.03      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 1.95/1.03      inference(cnf_transformation,[],[f31]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_2,plain,
% 1.95/1.03      ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
% 1.95/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1233,plain,
% 1.95/1.03      ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
% 1.95/1.03      inference(demodulation,[status(thm)],[c_1218,c_2]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1235,plain,
% 1.95/1.03      ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 1.95/1.03      inference(demodulation,[status(thm)],[c_1233,c_1218]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1762,plain,
% 1.95/1.03      ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k7_subset_1(k7_subset_1(X1,X1,X0),k7_subset_1(X1,X1,X0),k1_setfam_1(k2_tarski(X0,X1)))) = X1 ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_5,c_1235]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1917,plain,
% 1.95/1.03      ( k5_xboole_0(k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)),k7_subset_1(k1_xboole_0,k1_xboole_0,k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))) = sK1 ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_1261,c_1762]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_3,plain,
% 1.95/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.95/1.03      inference(cnf_transformation,[],[f28]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1,plain,
% 1.95/1.03      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.95/1.03      inference(cnf_transformation,[],[f45]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_839,plain,
% 1.95/1.03      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)))) = X0 ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_845,plain,
% 1.95/1.03      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 1.95/1.03      inference(light_normalisation,[status(thm)],[c_839,c_1,c_3]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1249,plain,
% 1.95/1.03      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_1218,c_845]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_824,plain,
% 1.95/1.03      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1251,plain,
% 1.95/1.03      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
% 1.95/1.03      inference(light_normalisation,[status(thm)],[c_1249,c_824]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1929,plain,
% 1.95/1.03      ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = sK1 ),
% 1.95/1.03      inference(demodulation,[status(thm)],[c_1917,c_3,c_1251]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1247,plain,
% 1.95/1.03      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_5,c_1218]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1406,plain,
% 1.95/1.03      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_693,c_1247]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1757,plain,
% 1.95/1.03      ( k5_xboole_0(k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)),k7_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))) = u1_struct_0(sK0) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_1406,c_1235]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1789,plain,
% 1.95/1.03      ( k5_xboole_0(k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))),k7_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))) = u1_struct_0(sK0) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_5,c_1757]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1793,plain,
% 1.95/1.03      ( k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1),sK1)) = u1_struct_0(sK0) ),
% 1.95/1.03      inference(light_normalisation,[status(thm)],[c_1789,c_693]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1243,plain,
% 1.95/1.03      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_1,c_1218]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1264,plain,
% 1.95/1.03      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 1.95/1.03      inference(light_normalisation,[status(thm)],[c_1243,c_3]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_970,plain,
% 1.95/1.03      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_446,c_432]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1246,plain,
% 1.95/1.03      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_970,c_1218]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1256,plain,
% 1.95/1.03      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 1.95/1.03      inference(light_normalisation,[status(thm)],[c_1246,c_4]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1217,plain,
% 1.95/1.03      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 1.95/1.03      inference(superposition,[status(thm)],[c_433,c_434]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1238,plain,
% 1.95/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 1.95/1.03      inference(demodulation,[status(thm)],[c_1217,c_1218]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_1220,plain,
% 1.95/1.03      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 1.95/1.03      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 1.95/1.03      inference(demodulation,[status(thm)],[c_1218,c_434]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_13,negated_conjecture,
% 1.95/1.03      ( k2_struct_0(sK0) != sK1
% 1.95/1.03      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 1.95/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.95/1.03  
% 1.95/1.03  cnf(c_10,negated_conjecture,
% 1.95/1.03      ( k2_struct_0(sK0) = sK1
% 1.95/1.03      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 1.95/1.03      inference(cnf_transformation,[],[f41]) ).
% 1.95/1.03  
% 1.95/1.03  
% 1.95/1.03  % SZS output end Saturation for theBenchmark.p
% 1.95/1.03  
% 1.95/1.03  ------                               Statistics
% 1.95/1.03  
% 1.95/1.03  ------ General
% 1.95/1.03  
% 1.95/1.03  abstr_ref_over_cycles:                  0
% 1.95/1.03  abstr_ref_under_cycles:                 0
% 1.95/1.03  gc_basic_clause_elim:                   0
% 1.95/1.03  forced_gc_time:                         0
% 1.95/1.03  parsing_time:                           0.012
% 1.95/1.03  unif_index_cands_time:                  0.
% 1.95/1.03  unif_index_add_time:                    0.
% 1.95/1.03  orderings_time:                         0.
% 1.95/1.03  out_proof_time:                         0.
% 1.95/1.03  total_time:                             0.126
% 1.95/1.03  num_of_symbols:                         44
% 1.95/1.03  num_of_terms:                           2504
% 1.95/1.03  
% 1.95/1.03  ------ Preprocessing
% 1.95/1.03  
% 1.95/1.03  num_of_splits:                          0
% 1.95/1.03  num_of_split_atoms:                     0
% 1.95/1.03  num_of_reused_defs:                     0
% 1.95/1.03  num_eq_ax_congr_red:                    5
% 1.95/1.03  num_of_sem_filtered_clauses:            1
% 1.95/1.03  num_of_subtypes:                        0
% 1.95/1.03  monotx_restored_types:                  0
% 1.95/1.03  sat_num_of_epr_types:                   0
% 1.95/1.03  sat_num_of_non_cyclic_types:            0
% 1.95/1.03  sat_guarded_non_collapsed_types:        0
% 1.95/1.03  num_pure_diseq_elim:                    0
% 1.95/1.03  simp_replaced_by:                       0
% 1.95/1.03  res_preprocessed:                       70
% 1.95/1.03  prep_upred:                             0
% 1.95/1.03  prep_unflattend:                        8
% 1.95/1.03  smt_new_axioms:                         0
% 1.95/1.03  pred_elim_cands:                        1
% 1.95/1.03  pred_elim:                              1
% 1.95/1.03  pred_elim_cl:                           1
% 1.95/1.03  pred_elim_cycles:                       3
% 1.95/1.03  merged_defs:                            8
% 1.95/1.03  merged_defs_ncl:                        0
% 1.95/1.03  bin_hyper_res:                          8
% 1.95/1.03  prep_cycles:                            4
% 1.95/1.03  pred_elim_time:                         0.002
% 1.95/1.03  splitting_time:                         0.
% 1.95/1.03  sem_filter_time:                        0.
% 1.95/1.03  monotx_time:                            0.018
% 1.95/1.03  subtype_inf_time:                       0.
% 1.95/1.03  
% 1.95/1.03  ------ Problem properties
% 1.95/1.03  
% 1.95/1.03  clauses:                                12
% 1.95/1.03  conjectures:                            3
% 1.95/1.03  epr:                                    0
% 1.95/1.03  horn:                                   11
% 1.95/1.03  ground:                                 3
% 1.95/1.03  unary:                                  8
% 1.95/1.03  binary:                                 4
% 1.95/1.03  lits:                                   16
% 1.95/1.03  lits_eq:                                12
% 1.95/1.03  fd_pure:                                0
% 1.95/1.03  fd_pseudo:                              0
% 1.95/1.03  fd_cond:                                0
% 1.95/1.03  fd_pseudo_cond:                         0
% 1.95/1.03  ac_symbols:                             0
% 1.95/1.03  
% 1.95/1.03  ------ Propositional Solver
% 1.95/1.03  
% 1.95/1.03  prop_solver_calls:                      27
% 1.95/1.03  prop_fast_solver_calls:                 295
% 1.95/1.03  smt_solver_calls:                       0
% 1.95/1.03  smt_fast_solver_calls:                  0
% 1.95/1.03  prop_num_of_clauses:                    757
% 1.95/1.03  prop_preprocess_simplified:             2348
% 1.95/1.03  prop_fo_subsumed:                       0
% 1.95/1.03  prop_solver_time:                       0.
% 1.95/1.03  smt_solver_time:                        0.
% 1.95/1.03  smt_fast_solver_time:                   0.
% 1.95/1.03  prop_fast_solver_time:                  0.
% 1.95/1.03  prop_unsat_core_time:                   0.
% 1.95/1.03  
% 1.95/1.03  ------ QBF
% 1.95/1.03  
% 1.95/1.03  qbf_q_res:                              0
% 1.95/1.03  qbf_num_tautologies:                    0
% 1.95/1.03  qbf_prep_cycles:                        0
% 1.95/1.03  
% 1.95/1.03  ------ BMC1
% 1.95/1.03  
% 1.95/1.03  bmc1_current_bound:                     -1
% 1.95/1.03  bmc1_last_solved_bound:                 -1
% 1.95/1.03  bmc1_unsat_core_size:                   -1
% 1.95/1.03  bmc1_unsat_core_parents_size:           -1
% 1.95/1.03  bmc1_merge_next_fun:                    0
% 1.95/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.95/1.03  
% 1.95/1.03  ------ Instantiation
% 1.95/1.03  
% 1.95/1.03  inst_num_of_clauses:                    278
% 1.95/1.03  inst_num_in_passive:                    70
% 1.95/1.03  inst_num_in_active:                     150
% 1.95/1.03  inst_num_in_unprocessed:                58
% 1.95/1.03  inst_num_of_loops:                      160
% 1.95/1.03  inst_num_of_learning_restarts:          0
% 1.95/1.03  inst_num_moves_active_passive:          7
% 1.95/1.03  inst_lit_activity:                      0
% 1.95/1.03  inst_lit_activity_moves:                0
% 1.95/1.03  inst_num_tautologies:                   0
% 1.95/1.03  inst_num_prop_implied:                  0
% 1.95/1.03  inst_num_existing_simplified:           0
% 1.95/1.03  inst_num_eq_res_simplified:             0
% 1.95/1.03  inst_num_child_elim:                    0
% 1.95/1.03  inst_num_of_dismatching_blockings:      143
% 1.95/1.03  inst_num_of_non_proper_insts:           235
% 1.95/1.03  inst_num_of_duplicates:                 0
% 1.95/1.03  inst_inst_num_from_inst_to_res:         0
% 1.95/1.03  inst_dismatching_checking_time:         0.
% 1.95/1.03  
% 1.95/1.03  ------ Resolution
% 1.95/1.03  
% 1.95/1.03  res_num_of_clauses:                     0
% 1.95/1.03  res_num_in_passive:                     0
% 1.95/1.03  res_num_in_active:                      0
% 1.95/1.03  res_num_of_loops:                       74
% 1.95/1.03  res_forward_subset_subsumed:            13
% 1.95/1.03  res_backward_subset_subsumed:           0
% 1.95/1.03  res_forward_subsumed:                   0
% 1.95/1.03  res_backward_subsumed:                  0
% 1.95/1.03  res_forward_subsumption_resolution:     0
% 1.95/1.03  res_backward_subsumption_resolution:    0
% 1.95/1.03  res_clause_to_clause_subsumption:       70
% 1.95/1.03  res_orphan_elimination:                 0
% 1.95/1.03  res_tautology_del:                      30
% 1.95/1.03  res_num_eq_res_simplified:              0
% 1.95/1.03  res_num_sel_changes:                    0
% 1.95/1.03  res_moves_from_active_to_pass:          0
% 1.95/1.03  
% 1.95/1.03  ------ Superposition
% 1.95/1.03  
% 1.95/1.03  sup_time_total:                         0.
% 1.95/1.03  sup_time_generating:                    0.
% 1.95/1.03  sup_time_sim_full:                      0.
% 1.95/1.03  sup_time_sim_immed:                     0.
% 1.95/1.03  
% 1.95/1.03  sup_num_of_clauses:                     31
% 1.95/1.03  sup_num_in_active:                      27
% 1.95/1.03  sup_num_in_passive:                     4
% 1.95/1.03  sup_num_of_loops:                       31
% 1.95/1.03  sup_fw_superposition:                   85
% 1.95/1.03  sup_bw_superposition:                   26
% 1.95/1.03  sup_immediate_simplified:               27
% 1.95/1.03  sup_given_eliminated:                   1
% 1.95/1.03  comparisons_done:                       0
% 1.95/1.03  comparisons_avoided:                    0
% 1.95/1.03  
% 1.95/1.03  ------ Simplifications
% 1.95/1.03  
% 1.95/1.03  
% 1.95/1.03  sim_fw_subset_subsumed:                 0
% 1.95/1.03  sim_bw_subset_subsumed:                 0
% 1.95/1.03  sim_fw_subsumed:                        3
% 1.95/1.03  sim_bw_subsumed:                        0
% 1.95/1.03  sim_fw_subsumption_res:                 0
% 1.95/1.03  sim_bw_subsumption_res:                 0
% 1.95/1.03  sim_tautology_del:                      1
% 1.95/1.03  sim_eq_tautology_del:                   15
% 1.95/1.03  sim_eq_res_simp:                        0
% 1.95/1.03  sim_fw_demodulated:                     16
% 1.95/1.03  sim_bw_demodulated:                     4
% 1.95/1.03  sim_light_normalised:                   22
% 1.95/1.03  sim_joinable_taut:                      0
% 1.95/1.03  sim_joinable_simp:                      0
% 1.95/1.03  sim_ac_normalised:                      0
% 1.95/1.03  sim_smt_subsumption:                    0
% 1.95/1.03  
%------------------------------------------------------------------------------
