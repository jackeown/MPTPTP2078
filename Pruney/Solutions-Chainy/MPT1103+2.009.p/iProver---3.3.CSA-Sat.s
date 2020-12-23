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
% DateTime   : Thu Dec  3 12:10:49 EST 2020

% Result     : CounterSatisfiable 2.56s
% Output     : Saturation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  124 (1380 expanded)
%              Number of clauses        :   64 ( 306 expanded)
%              Number of leaves         :   19 ( 370 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 (2208 expanded)
%              Number of equality atoms :  145 (1717 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ( ~ ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
          & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ( k2_struct_0(X0) = X1
          & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
        | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
          & k2_struct_0(X0) != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f29,plain,
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

fof(f30,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f35,f52,f53])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) = X0 ),
    inference(definition_unfolding,[],[f31,f53])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_111,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_7,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_596,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_606,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_596,c_5])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_594,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1569,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_606,c_594])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_593,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1568,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_593,c_594])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1804,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1568,c_3])).

cnf(c_3060,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1569,c_1804])).

cnf(c_3027,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1569,c_1568])).

cnf(c_3711,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3060,c_3027])).

cnf(c_1805,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1568,c_3])).

cnf(c_3028,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1569,c_1805])).

cnf(c_3671,plain,
    ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3028,c_3027])).

cnf(c_1,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3050,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1569])).

cnf(c_992,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_609,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_0,c_1])).

cnf(c_1166,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_992,c_1,c_609])).

cnf(c_3086,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3050,c_1166])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_130,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_10,c_2])).

cnf(c_592,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_130])).

cnf(c_893,plain,
    ( k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_593,c_592])).

cnf(c_3051,plain,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_893,c_1569])).

cnf(c_3083,plain,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3051,c_1166])).

cnf(c_4,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3052,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_1569])).

cnf(c_993,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X0,X1))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_3055,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1569,c_993])).

cnf(c_3078,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3052,c_3055])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_597,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1701,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_593,c_597])).

cnf(c_1953,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_4,c_1701])).

cnf(c_1964,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_1953,c_893])).

cnf(c_1967,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1964,c_1701])).

cnf(c_3057,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1569,c_1967])).

cnf(c_1585,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_893,c_993])).

cnf(c_3056,plain,
    ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1569,c_1585])).

cnf(c_3026,plain,
    ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1569,c_597])).

cnf(c_3025,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1569,c_3])).

cnf(c_2298,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1585,c_1568])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_595,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1174,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_593,c_595])).

cnf(c_1974,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1964,c_1174])).

cnf(c_1797,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1,c_1568])).

cnf(c_1824,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1797,c_1166])).

cnf(c_1798,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_893,c_1568])).

cnf(c_1821,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1798,c_1166])).

cnf(c_1702,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_606,c_597])).

cnf(c_1704,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1702,c_1,c_1166])).

cnf(c_1571,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1569,c_594])).

cnf(c_1169,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1166,c_609])).

cnf(c_14,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,negated_conjecture,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:14:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.56/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/0.99  
% 2.56/0.99  ------  iProver source info
% 2.56/0.99  
% 2.56/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.56/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/0.99  git: non_committed_changes: false
% 2.56/0.99  git: last_make_outside_of_git: false
% 2.56/0.99  
% 2.56/0.99  ------ 
% 2.56/0.99  
% 2.56/0.99  ------ Input Options
% 2.56/0.99  
% 2.56/0.99  --out_options                           all
% 2.56/0.99  --tptp_safe_out                         true
% 2.56/0.99  --problem_path                          ""
% 2.56/0.99  --include_path                          ""
% 2.56/0.99  --clausifier                            res/vclausify_rel
% 2.56/0.99  --clausifier_options                    --mode clausify
% 2.56/0.99  --stdin                                 false
% 2.56/0.99  --stats_out                             all
% 2.56/0.99  
% 2.56/0.99  ------ General Options
% 2.56/0.99  
% 2.56/0.99  --fof                                   false
% 2.56/0.99  --time_out_real                         305.
% 2.56/0.99  --time_out_virtual                      -1.
% 2.56/0.99  --symbol_type_check                     false
% 2.56/0.99  --clausify_out                          false
% 2.56/0.99  --sig_cnt_out                           false
% 2.56/0.99  --trig_cnt_out                          false
% 2.56/0.99  --trig_cnt_out_tolerance                1.
% 2.56/0.99  --trig_cnt_out_sk_spl                   false
% 2.56/0.99  --abstr_cl_out                          false
% 2.56/0.99  
% 2.56/0.99  ------ Global Options
% 2.56/0.99  
% 2.56/0.99  --schedule                              default
% 2.56/0.99  --add_important_lit                     false
% 2.56/0.99  --prop_solver_per_cl                    1000
% 2.56/0.99  --min_unsat_core                        false
% 2.56/0.99  --soft_assumptions                      false
% 2.56/0.99  --soft_lemma_size                       3
% 2.56/0.99  --prop_impl_unit_size                   0
% 2.56/0.99  --prop_impl_unit                        []
% 2.56/0.99  --share_sel_clauses                     true
% 2.56/0.99  --reset_solvers                         false
% 2.56/0.99  --bc_imp_inh                            [conj_cone]
% 2.56/0.99  --conj_cone_tolerance                   3.
% 2.56/0.99  --extra_neg_conj                        none
% 2.56/0.99  --large_theory_mode                     true
% 2.56/0.99  --prolific_symb_bound                   200
% 2.56/0.99  --lt_threshold                          2000
% 2.56/0.99  --clause_weak_htbl                      true
% 2.56/0.99  --gc_record_bc_elim                     false
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing Options
% 2.56/0.99  
% 2.56/0.99  --preprocessing_flag                    true
% 2.56/0.99  --time_out_prep_mult                    0.1
% 2.56/0.99  --splitting_mode                        input
% 2.56/0.99  --splitting_grd                         true
% 2.56/0.99  --splitting_cvd                         false
% 2.56/0.99  --splitting_cvd_svl                     false
% 2.56/0.99  --splitting_nvd                         32
% 2.56/0.99  --sub_typing                            true
% 2.56/0.99  --prep_gs_sim                           true
% 2.56/0.99  --prep_unflatten                        true
% 2.56/0.99  --prep_res_sim                          true
% 2.56/0.99  --prep_upred                            true
% 2.56/0.99  --prep_sem_filter                       exhaustive
% 2.56/0.99  --prep_sem_filter_out                   false
% 2.56/0.99  --pred_elim                             true
% 2.56/0.99  --res_sim_input                         true
% 2.56/0.99  --eq_ax_congr_red                       true
% 2.56/0.99  --pure_diseq_elim                       true
% 2.56/0.99  --brand_transform                       false
% 2.56/0.99  --non_eq_to_eq                          false
% 2.56/0.99  --prep_def_merge                        true
% 2.56/0.99  --prep_def_merge_prop_impl              false
% 2.56/0.99  --prep_def_merge_mbd                    true
% 2.56/0.99  --prep_def_merge_tr_red                 false
% 2.56/0.99  --prep_def_merge_tr_cl                  false
% 2.56/0.99  --smt_preprocessing                     true
% 2.56/0.99  --smt_ac_axioms                         fast
% 2.56/0.99  --preprocessed_out                      false
% 2.56/0.99  --preprocessed_stats                    false
% 2.56/0.99  
% 2.56/0.99  ------ Abstraction refinement Options
% 2.56/0.99  
% 2.56/0.99  --abstr_ref                             []
% 2.56/0.99  --abstr_ref_prep                        false
% 2.56/0.99  --abstr_ref_until_sat                   false
% 2.56/0.99  --abstr_ref_sig_restrict                funpre
% 2.56/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.99  --abstr_ref_under                       []
% 2.56/0.99  
% 2.56/0.99  ------ SAT Options
% 2.56/0.99  
% 2.56/0.99  --sat_mode                              false
% 2.56/0.99  --sat_fm_restart_options                ""
% 2.56/0.99  --sat_gr_def                            false
% 2.56/0.99  --sat_epr_types                         true
% 2.56/0.99  --sat_non_cyclic_types                  false
% 2.56/0.99  --sat_finite_models                     false
% 2.56/0.99  --sat_fm_lemmas                         false
% 2.56/0.99  --sat_fm_prep                           false
% 2.56/0.99  --sat_fm_uc_incr                        true
% 2.56/0.99  --sat_out_model                         small
% 2.56/0.99  --sat_out_clauses                       false
% 2.56/0.99  
% 2.56/0.99  ------ QBF Options
% 2.56/0.99  
% 2.56/0.99  --qbf_mode                              false
% 2.56/0.99  --qbf_elim_univ                         false
% 2.56/0.99  --qbf_dom_inst                          none
% 2.56/0.99  --qbf_dom_pre_inst                      false
% 2.56/0.99  --qbf_sk_in                             false
% 2.56/0.99  --qbf_pred_elim                         true
% 2.56/0.99  --qbf_split                             512
% 2.56/0.99  
% 2.56/0.99  ------ BMC1 Options
% 2.56/0.99  
% 2.56/0.99  --bmc1_incremental                      false
% 2.56/0.99  --bmc1_axioms                           reachable_all
% 2.56/0.99  --bmc1_min_bound                        0
% 2.56/0.99  --bmc1_max_bound                        -1
% 2.56/0.99  --bmc1_max_bound_default                -1
% 2.56/0.99  --bmc1_symbol_reachability              true
% 2.56/0.99  --bmc1_property_lemmas                  false
% 2.56/0.99  --bmc1_k_induction                      false
% 2.56/0.99  --bmc1_non_equiv_states                 false
% 2.56/0.99  --bmc1_deadlock                         false
% 2.56/0.99  --bmc1_ucm                              false
% 2.56/0.99  --bmc1_add_unsat_core                   none
% 2.56/0.99  --bmc1_unsat_core_children              false
% 2.56/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.99  --bmc1_out_stat                         full
% 2.56/0.99  --bmc1_ground_init                      false
% 2.56/0.99  --bmc1_pre_inst_next_state              false
% 2.56/0.99  --bmc1_pre_inst_state                   false
% 2.56/0.99  --bmc1_pre_inst_reach_state             false
% 2.56/0.99  --bmc1_out_unsat_core                   false
% 2.56/0.99  --bmc1_aig_witness_out                  false
% 2.56/0.99  --bmc1_verbose                          false
% 2.56/0.99  --bmc1_dump_clauses_tptp                false
% 2.56/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.99  --bmc1_dump_file                        -
% 2.56/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.99  --bmc1_ucm_extend_mode                  1
% 2.56/0.99  --bmc1_ucm_init_mode                    2
% 2.56/0.99  --bmc1_ucm_cone_mode                    none
% 2.56/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.99  --bmc1_ucm_relax_model                  4
% 2.56/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.99  --bmc1_ucm_layered_model                none
% 2.56/0.99  --bmc1_ucm_max_lemma_size               10
% 2.56/0.99  
% 2.56/0.99  ------ AIG Options
% 2.56/0.99  
% 2.56/0.99  --aig_mode                              false
% 2.56/0.99  
% 2.56/0.99  ------ Instantiation Options
% 2.56/0.99  
% 2.56/0.99  --instantiation_flag                    true
% 2.56/0.99  --inst_sos_flag                         false
% 2.56/0.99  --inst_sos_phase                        true
% 2.56/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.99  --inst_lit_sel_side                     num_symb
% 2.56/0.99  --inst_solver_per_active                1400
% 2.56/0.99  --inst_solver_calls_frac                1.
% 2.56/0.99  --inst_passive_queue_type               priority_queues
% 2.56/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.99  --inst_passive_queues_freq              [25;2]
% 2.56/0.99  --inst_dismatching                      true
% 2.56/0.99  --inst_eager_unprocessed_to_passive     true
% 2.56/0.99  --inst_prop_sim_given                   true
% 2.56/0.99  --inst_prop_sim_new                     false
% 2.56/0.99  --inst_subs_new                         false
% 2.56/0.99  --inst_eq_res_simp                      false
% 2.56/0.99  --inst_subs_given                       false
% 2.56/0.99  --inst_orphan_elimination               true
% 2.56/0.99  --inst_learning_loop_flag               true
% 2.56/0.99  --inst_learning_start                   3000
% 2.56/0.99  --inst_learning_factor                  2
% 2.56/0.99  --inst_start_prop_sim_after_learn       3
% 2.56/0.99  --inst_sel_renew                        solver
% 2.56/0.99  --inst_lit_activity_flag                true
% 2.56/0.99  --inst_restr_to_given                   false
% 2.56/0.99  --inst_activity_threshold               500
% 2.56/0.99  --inst_out_proof                        true
% 2.56/0.99  
% 2.56/0.99  ------ Resolution Options
% 2.56/0.99  
% 2.56/0.99  --resolution_flag                       true
% 2.56/0.99  --res_lit_sel                           adaptive
% 2.56/0.99  --res_lit_sel_side                      none
% 2.56/0.99  --res_ordering                          kbo
% 2.56/0.99  --res_to_prop_solver                    active
% 2.56/0.99  --res_prop_simpl_new                    false
% 2.56/0.99  --res_prop_simpl_given                  true
% 2.56/0.99  --res_passive_queue_type                priority_queues
% 2.56/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.99  --res_passive_queues_freq               [15;5]
% 2.56/0.99  --res_forward_subs                      full
% 2.56/0.99  --res_backward_subs                     full
% 2.56/0.99  --res_forward_subs_resolution           true
% 2.56/0.99  --res_backward_subs_resolution          true
% 2.56/0.99  --res_orphan_elimination                true
% 2.56/0.99  --res_time_limit                        2.
% 2.56/0.99  --res_out_proof                         true
% 2.56/0.99  
% 2.56/0.99  ------ Superposition Options
% 2.56/0.99  
% 2.56/0.99  --superposition_flag                    true
% 2.56/0.99  --sup_passive_queue_type                priority_queues
% 2.56/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.99  --demod_completeness_check              fast
% 2.56/0.99  --demod_use_ground                      true
% 2.56/0.99  --sup_to_prop_solver                    passive
% 2.56/0.99  --sup_prop_simpl_new                    true
% 2.56/0.99  --sup_prop_simpl_given                  true
% 2.56/0.99  --sup_fun_splitting                     false
% 2.56/0.99  --sup_smt_interval                      50000
% 2.56/0.99  
% 2.56/0.99  ------ Superposition Simplification Setup
% 2.56/0.99  
% 2.56/0.99  --sup_indices_passive                   []
% 2.56/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_full_bw                           [BwDemod]
% 2.56/0.99  --sup_immed_triv                        [TrivRules]
% 2.56/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_immed_bw_main                     []
% 2.56/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.99  
% 2.56/0.99  ------ Combination Options
% 2.56/0.99  
% 2.56/0.99  --comb_res_mult                         3
% 2.56/0.99  --comb_sup_mult                         2
% 2.56/0.99  --comb_inst_mult                        10
% 2.56/0.99  
% 2.56/0.99  ------ Debug Options
% 2.56/0.99  
% 2.56/0.99  --dbg_backtrace                         false
% 2.56/0.99  --dbg_dump_prop_clauses                 false
% 2.56/0.99  --dbg_dump_prop_clauses_file            -
% 2.56/0.99  --dbg_out_stat                          false
% 2.56/0.99  ------ Parsing...
% 2.56/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/0.99  ------ Proving...
% 2.56/0.99  ------ Problem Properties 
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  clauses                                 13
% 2.56/0.99  conjectures                             3
% 2.56/0.99  EPR                                     0
% 2.56/0.99  Horn                                    12
% 2.56/0.99  unary                                   7
% 2.56/0.99  binary                                  6
% 2.56/0.99  lits                                    19
% 2.56/0.99  lits eq                                 13
% 2.56/0.99  fd_pure                                 0
% 2.56/0.99  fd_pseudo                               0
% 2.56/0.99  fd_cond                                 0
% 2.56/0.99  fd_pseudo_cond                          0
% 2.56/0.99  AC symbols                              0
% 2.56/0.99  
% 2.56/0.99  ------ Schedule dynamic 5 is on 
% 2.56/0.99  
% 2.56/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  ------ 
% 2.56/0.99  Current options:
% 2.56/0.99  ------ 
% 2.56/0.99  
% 2.56/0.99  ------ Input Options
% 2.56/0.99  
% 2.56/0.99  --out_options                           all
% 2.56/0.99  --tptp_safe_out                         true
% 2.56/0.99  --problem_path                          ""
% 2.56/0.99  --include_path                          ""
% 2.56/0.99  --clausifier                            res/vclausify_rel
% 2.56/0.99  --clausifier_options                    --mode clausify
% 2.56/0.99  --stdin                                 false
% 2.56/0.99  --stats_out                             all
% 2.56/0.99  
% 2.56/0.99  ------ General Options
% 2.56/0.99  
% 2.56/0.99  --fof                                   false
% 2.56/0.99  --time_out_real                         305.
% 2.56/0.99  --time_out_virtual                      -1.
% 2.56/0.99  --symbol_type_check                     false
% 2.56/0.99  --clausify_out                          false
% 2.56/0.99  --sig_cnt_out                           false
% 2.56/0.99  --trig_cnt_out                          false
% 2.56/0.99  --trig_cnt_out_tolerance                1.
% 2.56/0.99  --trig_cnt_out_sk_spl                   false
% 2.56/0.99  --abstr_cl_out                          false
% 2.56/0.99  
% 2.56/0.99  ------ Global Options
% 2.56/0.99  
% 2.56/0.99  --schedule                              default
% 2.56/0.99  --add_important_lit                     false
% 2.56/0.99  --prop_solver_per_cl                    1000
% 2.56/0.99  --min_unsat_core                        false
% 2.56/0.99  --soft_assumptions                      false
% 2.56/0.99  --soft_lemma_size                       3
% 2.56/0.99  --prop_impl_unit_size                   0
% 2.56/0.99  --prop_impl_unit                        []
% 2.56/0.99  --share_sel_clauses                     true
% 2.56/0.99  --reset_solvers                         false
% 2.56/0.99  --bc_imp_inh                            [conj_cone]
% 2.56/0.99  --conj_cone_tolerance                   3.
% 2.56/0.99  --extra_neg_conj                        none
% 2.56/0.99  --large_theory_mode                     true
% 2.56/0.99  --prolific_symb_bound                   200
% 2.56/0.99  --lt_threshold                          2000
% 2.56/0.99  --clause_weak_htbl                      true
% 2.56/0.99  --gc_record_bc_elim                     false
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing Options
% 2.56/0.99  
% 2.56/0.99  --preprocessing_flag                    true
% 2.56/0.99  --time_out_prep_mult                    0.1
% 2.56/0.99  --splitting_mode                        input
% 2.56/0.99  --splitting_grd                         true
% 2.56/0.99  --splitting_cvd                         false
% 2.56/0.99  --splitting_cvd_svl                     false
% 2.56/0.99  --splitting_nvd                         32
% 2.56/0.99  --sub_typing                            true
% 2.56/0.99  --prep_gs_sim                           true
% 2.56/0.99  --prep_unflatten                        true
% 2.56/0.99  --prep_res_sim                          true
% 2.56/0.99  --prep_upred                            true
% 2.56/0.99  --prep_sem_filter                       exhaustive
% 2.56/0.99  --prep_sem_filter_out                   false
% 2.56/0.99  --pred_elim                             true
% 2.56/0.99  --res_sim_input                         true
% 2.56/0.99  --eq_ax_congr_red                       true
% 2.56/0.99  --pure_diseq_elim                       true
% 2.56/0.99  --brand_transform                       false
% 2.56/0.99  --non_eq_to_eq                          false
% 2.56/0.99  --prep_def_merge                        true
% 2.56/0.99  --prep_def_merge_prop_impl              false
% 2.56/0.99  --prep_def_merge_mbd                    true
% 2.56/0.99  --prep_def_merge_tr_red                 false
% 2.56/0.99  --prep_def_merge_tr_cl                  false
% 2.56/0.99  --smt_preprocessing                     true
% 2.56/0.99  --smt_ac_axioms                         fast
% 2.56/0.99  --preprocessed_out                      false
% 2.56/0.99  --preprocessed_stats                    false
% 2.56/0.99  
% 2.56/0.99  ------ Abstraction refinement Options
% 2.56/0.99  
% 2.56/0.99  --abstr_ref                             []
% 2.56/0.99  --abstr_ref_prep                        false
% 2.56/0.99  --abstr_ref_until_sat                   false
% 2.56/0.99  --abstr_ref_sig_restrict                funpre
% 2.56/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.99  --abstr_ref_under                       []
% 2.56/0.99  
% 2.56/0.99  ------ SAT Options
% 2.56/0.99  
% 2.56/0.99  --sat_mode                              false
% 2.56/0.99  --sat_fm_restart_options                ""
% 2.56/0.99  --sat_gr_def                            false
% 2.56/0.99  --sat_epr_types                         true
% 2.56/0.99  --sat_non_cyclic_types                  false
% 2.56/0.99  --sat_finite_models                     false
% 2.56/0.99  --sat_fm_lemmas                         false
% 2.56/0.99  --sat_fm_prep                           false
% 2.56/0.99  --sat_fm_uc_incr                        true
% 2.56/0.99  --sat_out_model                         small
% 2.56/0.99  --sat_out_clauses                       false
% 2.56/0.99  
% 2.56/0.99  ------ QBF Options
% 2.56/0.99  
% 2.56/0.99  --qbf_mode                              false
% 2.56/0.99  --qbf_elim_univ                         false
% 2.56/0.99  --qbf_dom_inst                          none
% 2.56/0.99  --qbf_dom_pre_inst                      false
% 2.56/0.99  --qbf_sk_in                             false
% 2.56/0.99  --qbf_pred_elim                         true
% 2.56/0.99  --qbf_split                             512
% 2.56/0.99  
% 2.56/0.99  ------ BMC1 Options
% 2.56/0.99  
% 2.56/0.99  --bmc1_incremental                      false
% 2.56/0.99  --bmc1_axioms                           reachable_all
% 2.56/0.99  --bmc1_min_bound                        0
% 2.56/0.99  --bmc1_max_bound                        -1
% 2.56/0.99  --bmc1_max_bound_default                -1
% 2.56/0.99  --bmc1_symbol_reachability              true
% 2.56/0.99  --bmc1_property_lemmas                  false
% 2.56/0.99  --bmc1_k_induction                      false
% 2.56/0.99  --bmc1_non_equiv_states                 false
% 2.56/0.99  --bmc1_deadlock                         false
% 2.56/0.99  --bmc1_ucm                              false
% 2.56/0.99  --bmc1_add_unsat_core                   none
% 2.56/0.99  --bmc1_unsat_core_children              false
% 2.56/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.99  --bmc1_out_stat                         full
% 2.56/0.99  --bmc1_ground_init                      false
% 2.56/0.99  --bmc1_pre_inst_next_state              false
% 2.56/0.99  --bmc1_pre_inst_state                   false
% 2.56/0.99  --bmc1_pre_inst_reach_state             false
% 2.56/0.99  --bmc1_out_unsat_core                   false
% 2.56/0.99  --bmc1_aig_witness_out                  false
% 2.56/0.99  --bmc1_verbose                          false
% 2.56/0.99  --bmc1_dump_clauses_tptp                false
% 2.56/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.99  --bmc1_dump_file                        -
% 2.56/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.99  --bmc1_ucm_extend_mode                  1
% 2.56/0.99  --bmc1_ucm_init_mode                    2
% 2.56/0.99  --bmc1_ucm_cone_mode                    none
% 2.56/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.99  --bmc1_ucm_relax_model                  4
% 2.56/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.99  --bmc1_ucm_layered_model                none
% 2.56/0.99  --bmc1_ucm_max_lemma_size               10
% 2.56/0.99  
% 2.56/0.99  ------ AIG Options
% 2.56/0.99  
% 2.56/0.99  --aig_mode                              false
% 2.56/0.99  
% 2.56/0.99  ------ Instantiation Options
% 2.56/0.99  
% 2.56/0.99  --instantiation_flag                    true
% 2.56/0.99  --inst_sos_flag                         false
% 2.56/0.99  --inst_sos_phase                        true
% 2.56/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.99  --inst_lit_sel_side                     none
% 2.56/0.99  --inst_solver_per_active                1400
% 2.56/0.99  --inst_solver_calls_frac                1.
% 2.56/0.99  --inst_passive_queue_type               priority_queues
% 2.56/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.99  --inst_passive_queues_freq              [25;2]
% 2.56/0.99  --inst_dismatching                      true
% 2.56/0.99  --inst_eager_unprocessed_to_passive     true
% 2.56/0.99  --inst_prop_sim_given                   true
% 2.56/0.99  --inst_prop_sim_new                     false
% 2.56/0.99  --inst_subs_new                         false
% 2.56/0.99  --inst_eq_res_simp                      false
% 2.56/0.99  --inst_subs_given                       false
% 2.56/0.99  --inst_orphan_elimination               true
% 2.56/0.99  --inst_learning_loop_flag               true
% 2.56/0.99  --inst_learning_start                   3000
% 2.56/0.99  --inst_learning_factor                  2
% 2.56/0.99  --inst_start_prop_sim_after_learn       3
% 2.56/0.99  --inst_sel_renew                        solver
% 2.56/0.99  --inst_lit_activity_flag                true
% 2.56/0.99  --inst_restr_to_given                   false
% 2.56/0.99  --inst_activity_threshold               500
% 2.56/0.99  --inst_out_proof                        true
% 2.56/0.99  
% 2.56/0.99  ------ Resolution Options
% 2.56/0.99  
% 2.56/0.99  --resolution_flag                       false
% 2.56/0.99  --res_lit_sel                           adaptive
% 2.56/0.99  --res_lit_sel_side                      none
% 2.56/0.99  --res_ordering                          kbo
% 2.56/0.99  --res_to_prop_solver                    active
% 2.56/0.99  --res_prop_simpl_new                    false
% 2.56/0.99  --res_prop_simpl_given                  true
% 2.56/0.99  --res_passive_queue_type                priority_queues
% 2.56/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.99  --res_passive_queues_freq               [15;5]
% 2.56/0.99  --res_forward_subs                      full
% 2.56/0.99  --res_backward_subs                     full
% 2.56/0.99  --res_forward_subs_resolution           true
% 2.56/0.99  --res_backward_subs_resolution          true
% 2.56/0.99  --res_orphan_elimination                true
% 2.56/0.99  --res_time_limit                        2.
% 2.56/0.99  --res_out_proof                         true
% 2.56/0.99  
% 2.56/0.99  ------ Superposition Options
% 2.56/0.99  
% 2.56/0.99  --superposition_flag                    true
% 2.56/0.99  --sup_passive_queue_type                priority_queues
% 2.56/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.99  --demod_completeness_check              fast
% 2.56/0.99  --demod_use_ground                      true
% 2.56/0.99  --sup_to_prop_solver                    passive
% 2.56/0.99  --sup_prop_simpl_new                    true
% 2.56/0.99  --sup_prop_simpl_given                  true
% 2.56/0.99  --sup_fun_splitting                     false
% 2.56/0.99  --sup_smt_interval                      50000
% 2.56/0.99  
% 2.56/0.99  ------ Superposition Simplification Setup
% 2.56/0.99  
% 2.56/0.99  --sup_indices_passive                   []
% 2.56/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_full_bw                           [BwDemod]
% 2.56/0.99  --sup_immed_triv                        [TrivRules]
% 2.56/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_immed_bw_main                     []
% 2.56/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.99  
% 2.56/0.99  ------ Combination Options
% 2.56/0.99  
% 2.56/0.99  --comb_res_mult                         3
% 2.56/0.99  --comb_sup_mult                         2
% 2.56/0.99  --comb_inst_mult                        10
% 2.56/0.99  
% 2.56/0.99  ------ Debug Options
% 2.56/0.99  
% 2.56/0.99  --dbg_backtrace                         false
% 2.56/0.99  --dbg_dump_prop_clauses                 false
% 2.56/0.99  --dbg_dump_prop_clauses_file            -
% 2.56/0.99  --dbg_out_stat                          false
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  ------ Proving...
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  % SZS output start Saturation for theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  fof(f11,axiom,(
% 2.56/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f41,plain,(
% 2.56/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f11])).
% 2.56/0.99  
% 2.56/0.99  fof(f14,axiom,(
% 2.56/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f44,plain,(
% 2.56/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f14])).
% 2.56/0.99  
% 2.56/0.99  fof(f8,axiom,(
% 2.56/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f38,plain,(
% 2.56/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f8])).
% 2.56/0.99  
% 2.56/0.99  fof(f54,plain,(
% 2.56/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.56/0.99    inference(definition_unfolding,[],[f44,f38])).
% 2.56/0.99  
% 2.56/0.99  fof(f61,plain,(
% 2.56/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.56/0.99    inference(definition_unfolding,[],[f41,f54])).
% 2.56/0.99  
% 2.56/0.99  fof(f9,axiom,(
% 2.56/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f39,plain,(
% 2.56/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.56/0.99    inference(cnf_transformation,[],[f9])).
% 2.56/0.99  
% 2.56/0.99  fof(f59,plain,(
% 2.56/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.56/0.99    inference(definition_unfolding,[],[f39,f54])).
% 2.56/0.99  
% 2.56/0.99  fof(f13,axiom,(
% 2.56/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f26,plain,(
% 2.56/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.56/0.99    inference(ennf_transformation,[],[f13])).
% 2.56/0.99  
% 2.56/0.99  fof(f43,plain,(
% 2.56/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f26])).
% 2.56/0.99  
% 2.56/0.99  fof(f3,axiom,(
% 2.56/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f33,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f3])).
% 2.56/0.99  
% 2.56/0.99  fof(f15,axiom,(
% 2.56/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f45,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f15])).
% 2.56/0.99  
% 2.56/0.99  fof(f52,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.56/0.99    inference(definition_unfolding,[],[f33,f45])).
% 2.56/0.99  
% 2.56/0.99  fof(f62,plain,(
% 2.56/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.56/0.99    inference(definition_unfolding,[],[f43,f52])).
% 2.56/0.99  
% 2.56/0.99  fof(f17,conjecture,(
% 2.56/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f18,negated_conjecture,(
% 2.56/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.56/0.99    inference(negated_conjecture,[],[f17])).
% 2.56/0.99  
% 2.56/0.99  fof(f22,plain,(
% 2.56/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)))),
% 2.56/0.99    inference(pure_predicate_removal,[],[f18])).
% 2.56/0.99  
% 2.56/0.99  fof(f28,plain,(
% 2.56/0.99    ? [X0,X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 2.56/0.99    inference(ennf_transformation,[],[f22])).
% 2.56/0.99  
% 2.56/0.99  fof(f29,plain,(
% 2.56/0.99    ? [X0,X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.56/0.99    introduced(choice_axiom,[])).
% 2.56/0.99  
% 2.56/0.99  fof(f30,plain,(
% 2.56/0.99    ((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 2.56/0.99  
% 2.56/0.99  fof(f47,plain,(
% 2.56/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.56/0.99    inference(cnf_transformation,[],[f30])).
% 2.56/0.99  
% 2.56/0.99  fof(f5,axiom,(
% 2.56/0.99    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f35,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.56/0.99    inference(cnf_transformation,[],[f5])).
% 2.56/0.99  
% 2.56/0.99  fof(f6,axiom,(
% 2.56/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f36,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f6])).
% 2.56/0.99  
% 2.56/0.99  fof(f53,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 2.56/0.99    inference(definition_unfolding,[],[f36,f52])).
% 2.56/0.99  
% 2.56/0.99  fof(f58,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0) )),
% 2.56/0.99    inference(definition_unfolding,[],[f35,f52,f53])).
% 2.56/0.99  
% 2.56/0.99  fof(f2,axiom,(
% 2.56/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f20,plain,(
% 2.56/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.56/0.99    inference(rectify,[],[f2])).
% 2.56/0.99  
% 2.56/0.99  fof(f32,plain,(
% 2.56/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.56/0.99    inference(cnf_transformation,[],[f20])).
% 2.56/0.99  
% 2.56/0.99  fof(f56,plain,(
% 2.56/0.99    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.56/0.99    inference(definition_unfolding,[],[f32,f45])).
% 2.56/0.99  
% 2.56/0.99  fof(f1,axiom,(
% 2.56/0.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f19,plain,(
% 2.56/0.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.56/0.99    inference(rectify,[],[f1])).
% 2.56/0.99  
% 2.56/0.99  fof(f31,plain,(
% 2.56/0.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.56/0.99    inference(cnf_transformation,[],[f19])).
% 2.56/0.99  
% 2.56/0.99  fof(f55,plain,(
% 2.56/0.99    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) = X0) )),
% 2.56/0.99    inference(definition_unfolding,[],[f31,f53])).
% 2.56/0.99  
% 2.56/0.99  fof(f16,axiom,(
% 2.56/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f21,plain,(
% 2.56/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.56/0.99    inference(unused_predicate_definition_removal,[],[f16])).
% 2.56/0.99  
% 2.56/0.99  fof(f27,plain,(
% 2.56/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.56/0.99    inference(ennf_transformation,[],[f21])).
% 2.56/0.99  
% 2.56/0.99  fof(f46,plain,(
% 2.56/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f27])).
% 2.56/0.99  
% 2.56/0.99  fof(f4,axiom,(
% 2.56/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f23,plain,(
% 2.56/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.56/0.99    inference(ennf_transformation,[],[f4])).
% 2.56/0.99  
% 2.56/0.99  fof(f34,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f23])).
% 2.56/0.99  
% 2.56/0.99  fof(f57,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.56/0.99    inference(definition_unfolding,[],[f34,f45])).
% 2.56/0.99  
% 2.56/0.99  fof(f7,axiom,(
% 2.56/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f37,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.56/0.99    inference(cnf_transformation,[],[f7])).
% 2.56/0.99  
% 2.56/0.99  fof(f10,axiom,(
% 2.56/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f24,plain,(
% 2.56/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.56/0.99    inference(ennf_transformation,[],[f10])).
% 2.56/0.99  
% 2.56/0.99  fof(f40,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f24])).
% 2.56/0.99  
% 2.56/0.99  fof(f60,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.56/0.99    inference(definition_unfolding,[],[f40,f52])).
% 2.56/0.99  
% 2.56/0.99  fof(f12,axiom,(
% 2.56/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.56/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.99  
% 2.56/0.99  fof(f25,plain,(
% 2.56/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.56/0.99    inference(ennf_transformation,[],[f12])).
% 2.56/0.99  
% 2.56/0.99  fof(f42,plain,(
% 2.56/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.56/0.99    inference(cnf_transformation,[],[f25])).
% 2.56/0.99  
% 2.56/0.99  fof(f48,plain,(
% 2.56/0.99    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1),
% 2.56/0.99    inference(cnf_transformation,[],[f30])).
% 2.56/0.99  
% 2.56/0.99  fof(f51,plain,(
% 2.56/0.99    k2_struct_0(sK0) = sK1 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 2.56/0.99    inference(cnf_transformation,[],[f30])).
% 2.56/0.99  
% 2.56/0.99  cnf(c_111,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_7,plain,
% 2.56/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 2.56/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_596,plain,
% 2.56/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_5,plain,
% 2.56/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_606,plain,
% 2.56/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.56/0.99      inference(light_normalisation,[status(thm)],[c_596,c_5]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_9,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.56/0.99      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.56/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_594,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.56/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1569,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_606,c_594]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_15,negated_conjecture,
% 2.56/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.56/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_593,plain,
% 2.56/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1568,plain,
% 2.56/0.99      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_593,c_594]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1804,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0))))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1568,c_3]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3060,plain,
% 2.56/0.99      ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1569,c_1804]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3027,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1569,c_1568]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3711,plain,
% 2.56/0.99      ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k1_xboole_0 ),
% 2.56/0.99      inference(light_normalisation,[status(thm)],[c_3060,c_3027]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1805,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1568,c_3]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3028,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1569,c_1805]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3671,plain,
% 2.56/0.99      ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_3028,c_3027]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1,plain,
% 2.56/0.99      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3050,plain,
% 2.56/0.99      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1,c_1569]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_992,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_0,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) = X0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_609,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 2.56/0.99      inference(light_normalisation,[status(thm)],[c_0,c_1]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1166,plain,
% 2.56/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.56/0.99      inference(light_normalisation,[status(thm)],[c_992,c_1,c_609]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3086,plain,
% 2.56/0.99      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 2.56/0.99      inference(light_normalisation,[status(thm)],[c_3050,c_1166]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_10,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.56/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2,plain,
% 2.56/0.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_130,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.56/0.99      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 2.56/0.99      inference(resolution,[status(thm)],[c_10,c_2]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_592,plain,
% 2.56/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 2.56/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_130]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_893,plain,
% 2.56/0.99      ( k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = sK1 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_593,c_592]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3051,plain,
% 2.56/0.99      ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_893,c_1569]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3083,plain,
% 2.56/0.99      ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_3051,c_1166]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_4,plain,
% 2.56/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.56/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3052,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_4,c_1569]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_993,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X0,X1))))))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3055,plain,
% 2.56/0.99      ( k7_subset_1(X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X0,X1))))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1569,c_993]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3078,plain,
% 2.56/0.99      ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) = k1_xboole_0 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_3052,c_3055]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_6,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.56/0.99      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 2.56/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_597,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 2.56/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1701,plain,
% 2.56/0.99      ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_593,c_597]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1953,plain,
% 2.56/0.99      ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_4,c_1701]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1964,plain,
% 2.56/0.99      ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
% 2.56/0.99      inference(light_normalisation,[status(thm)],[c_1953,c_893]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1967,plain,
% 2.56/0.99      ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1964,c_1701]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3057,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1569,c_1967]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1585,plain,
% 2.56/0.99      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_893,c_993]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3056,plain,
% 2.56/0.99      ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1569,c_1585]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3026,plain,
% 2.56/0.99      ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
% 2.56/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1569,c_597]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_3025,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k1_xboole_0 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1569,c_3]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_2298,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1585,c_1568]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_8,plain,
% 2.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.56/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.56/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_595,plain,
% 2.56/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 2.56/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.56/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1174,plain,
% 2.56/0.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_593,c_595]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1974,plain,
% 2.56/0.99      ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1964,c_1174]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1797,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_1,c_1568]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1824,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_xboole_0 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1797,c_1166]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1798,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_893,c_1568]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1821,plain,
% 2.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1798,c_1166]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1702,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k3_subset_1(X0,X0) ),
% 2.56/0.99      inference(superposition,[status(thm)],[c_606,c_597]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1704,plain,
% 2.56/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 2.56/0.99      inference(light_normalisation,[status(thm)],[c_1702,c_1,c_1166]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1571,plain,
% 2.56/0.99      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 2.56/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1569,c_594]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_1169,plain,
% 2.56/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.56/0.99      inference(demodulation,[status(thm)],[c_1166,c_609]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_14,negated_conjecture,
% 2.56/0.99      ( k2_struct_0(sK0) != sK1
% 2.56/0.99      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.56/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.56/0.99  
% 2.56/0.99  cnf(c_11,negated_conjecture,
% 2.56/0.99      ( k2_struct_0(sK0) = sK1
% 2.56/0.99      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.56/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  % SZS output end Saturation for theBenchmark.p
% 2.56/0.99  
% 2.56/0.99  ------                               Statistics
% 2.56/0.99  
% 2.56/0.99  ------ General
% 2.56/0.99  
% 2.56/0.99  abstr_ref_over_cycles:                  0
% 2.56/0.99  abstr_ref_under_cycles:                 0
% 2.56/0.99  gc_basic_clause_elim:                   0
% 2.56/0.99  forced_gc_time:                         0
% 2.56/0.99  parsing_time:                           0.007
% 2.56/0.99  unif_index_cands_time:                  0.
% 2.56/0.99  unif_index_add_time:                    0.
% 2.56/0.99  orderings_time:                         0.
% 2.56/0.99  out_proof_time:                         0.
% 2.56/0.99  total_time:                             0.163
% 2.56/0.99  num_of_symbols:                         44
% 2.56/0.99  num_of_terms:                           4656
% 2.56/0.99  
% 2.56/0.99  ------ Preprocessing
% 2.56/0.99  
% 2.56/0.99  num_of_splits:                          0
% 2.56/0.99  num_of_split_atoms:                     0
% 2.56/0.99  num_of_reused_defs:                     0
% 2.56/0.99  num_eq_ax_congr_red:                    11
% 2.56/0.99  num_of_sem_filtered_clauses:            1
% 2.56/0.99  num_of_subtypes:                        0
% 2.56/0.99  monotx_restored_types:                  0
% 2.56/0.99  sat_num_of_epr_types:                   0
% 2.56/0.99  sat_num_of_non_cyclic_types:            0
% 2.56/0.99  sat_guarded_non_collapsed_types:        0
% 2.56/0.99  num_pure_diseq_elim:                    0
% 2.56/0.99  simp_replaced_by:                       0
% 2.56/0.99  res_preprocessed:                       76
% 2.56/0.99  prep_upred:                             0
% 2.56/0.99  prep_unflattend:                        16
% 2.56/0.99  smt_new_axioms:                         0
% 2.56/0.99  pred_elim_cands:                        1
% 2.56/0.99  pred_elim:                              1
% 2.56/0.99  pred_elim_cl:                           1
% 2.56/0.99  pred_elim_cycles:                       3
% 2.56/0.99  merged_defs:                            8
% 2.56/0.99  merged_defs_ncl:                        0
% 2.56/0.99  bin_hyper_res:                          8
% 2.56/0.99  prep_cycles:                            4
% 2.56/0.99  pred_elim_time:                         0.003
% 2.56/0.99  splitting_time:                         0.
% 2.56/0.99  sem_filter_time:                        0.
% 2.56/0.99  monotx_time:                            0.
% 2.56/0.99  subtype_inf_time:                       0.
% 2.56/0.99  
% 2.56/0.99  ------ Problem properties
% 2.56/0.99  
% 2.56/0.99  clauses:                                13
% 2.56/0.99  conjectures:                            3
% 2.56/0.99  epr:                                    0
% 2.56/0.99  horn:                                   12
% 2.56/0.99  ground:                                 3
% 2.56/0.99  unary:                                  7
% 2.56/0.99  binary:                                 6
% 2.56/0.99  lits:                                   19
% 2.56/0.99  lits_eq:                                13
% 2.56/0.99  fd_pure:                                0
% 2.56/0.99  fd_pseudo:                              0
% 2.56/0.99  fd_cond:                                0
% 2.56/0.99  fd_pseudo_cond:                         0
% 2.56/0.99  ac_symbols:                             0
% 2.56/0.99  
% 2.56/0.99  ------ Propositional Solver
% 2.56/0.99  
% 2.56/0.99  prop_solver_calls:                      28
% 2.56/0.99  prop_fast_solver_calls:                 368
% 2.56/0.99  smt_solver_calls:                       0
% 2.56/0.99  smt_fast_solver_calls:                  0
% 2.56/0.99  prop_num_of_clauses:                    1665
% 2.56/0.99  prop_preprocess_simplified:             4292
% 2.56/0.99  prop_fo_subsumed:                       0
% 2.56/0.99  prop_solver_time:                       0.
% 2.56/0.99  smt_solver_time:                        0.
% 2.56/0.99  smt_fast_solver_time:                   0.
% 2.56/0.99  prop_fast_solver_time:                  0.
% 2.56/0.99  prop_unsat_core_time:                   0.
% 2.56/0.99  
% 2.56/0.99  ------ QBF
% 2.56/0.99  
% 2.56/0.99  qbf_q_res:                              0
% 2.56/0.99  qbf_num_tautologies:                    0
% 2.56/0.99  qbf_prep_cycles:                        0
% 2.56/0.99  
% 2.56/0.99  ------ BMC1
% 2.56/0.99  
% 2.56/0.99  bmc1_current_bound:                     -1
% 2.56/0.99  bmc1_last_solved_bound:                 -1
% 2.56/0.99  bmc1_unsat_core_size:                   -1
% 2.56/0.99  bmc1_unsat_core_parents_size:           -1
% 2.56/0.99  bmc1_merge_next_fun:                    0
% 2.56/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.56/0.99  
% 2.56/0.99  ------ Instantiation
% 2.56/0.99  
% 2.56/0.99  inst_num_of_clauses:                    609
% 2.56/0.99  inst_num_in_passive:                    230
% 2.56/0.99  inst_num_in_active:                     269
% 2.56/0.99  inst_num_in_unprocessed:                110
% 2.56/0.99  inst_num_of_loops:                      280
% 2.56/0.99  inst_num_of_learning_restarts:          0
% 2.56/0.99  inst_num_moves_active_passive:          8
% 2.56/0.99  inst_lit_activity:                      0
% 2.56/0.99  inst_lit_activity_moves:                0
% 2.56/0.99  inst_num_tautologies:                   0
% 2.56/0.99  inst_num_prop_implied:                  0
% 2.56/0.99  inst_num_existing_simplified:           0
% 2.56/0.99  inst_num_eq_res_simplified:             0
% 2.56/0.99  inst_num_child_elim:                    0
% 2.56/0.99  inst_num_of_dismatching_blockings:      309
% 2.56/0.99  inst_num_of_non_proper_insts:           470
% 2.56/0.99  inst_num_of_duplicates:                 0
% 2.56/0.99  inst_inst_num_from_inst_to_res:         0
% 2.56/0.99  inst_dismatching_checking_time:         0.
% 2.56/0.99  
% 2.56/0.99  ------ Resolution
% 2.56/0.99  
% 2.56/0.99  res_num_of_clauses:                     0
% 2.56/0.99  res_num_in_passive:                     0
% 2.56/0.99  res_num_in_active:                      0
% 2.56/0.99  res_num_of_loops:                       80
% 2.56/0.99  res_forward_subset_subsumed:            23
% 2.56/0.99  res_backward_subset_subsumed:           0
% 2.56/0.99  res_forward_subsumed:                   0
% 2.56/0.99  res_backward_subsumed:                  0
% 2.56/0.99  res_forward_subsumption_resolution:     0
% 2.56/0.99  res_backward_subsumption_resolution:    0
% 2.56/0.99  res_clause_to_clause_subsumption:       191
% 2.56/0.99  res_orphan_elimination:                 0
% 2.56/0.99  res_tautology_del:                      44
% 2.56/0.99  res_num_eq_res_simplified:              0
% 2.56/0.99  res_num_sel_changes:                    0
% 2.56/0.99  res_moves_from_active_to_pass:          0
% 2.56/0.99  
% 2.56/0.99  ------ Superposition
% 2.56/0.99  
% 2.56/0.99  sup_time_total:                         0.
% 2.56/0.99  sup_time_generating:                    0.
% 2.56/0.99  sup_time_sim_full:                      0.
% 2.56/0.99  sup_time_sim_immed:                     0.
% 2.56/0.99  
% 2.56/0.99  sup_num_of_clauses:                     43
% 2.56/0.99  sup_num_in_active:                      34
% 2.56/0.99  sup_num_in_passive:                     9
% 2.56/0.99  sup_num_of_loops:                       54
% 2.56/0.99  sup_fw_superposition:                   121
% 2.56/0.99  sup_bw_superposition:                   68
% 2.56/0.99  sup_immediate_simplified:               45
% 2.56/0.99  sup_given_eliminated:                   2
% 2.56/0.99  comparisons_done:                       0
% 2.56/0.99  comparisons_avoided:                    0
% 2.56/0.99  
% 2.56/0.99  ------ Simplifications
% 2.56/0.99  
% 2.56/0.99  
% 2.56/0.99  sim_fw_subset_subsumed:                 0
% 2.56/0.99  sim_bw_subset_subsumed:                 0
% 2.56/0.99  sim_fw_subsumed:                        3
% 2.56/0.99  sim_bw_subsumed:                        4
% 2.56/0.99  sim_fw_subsumption_res:                 0
% 2.56/0.99  sim_bw_subsumption_res:                 0
% 2.56/0.99  sim_tautology_del:                      1
% 2.56/0.99  sim_eq_tautology_del:                   30
% 2.56/0.99  sim_eq_res_simp:                        0
% 2.56/0.99  sim_fw_demodulated:                     29
% 2.56/0.99  sim_bw_demodulated:                     24
% 2.56/0.99  sim_light_normalised:                   21
% 2.56/0.99  sim_joinable_taut:                      0
% 2.56/0.99  sim_joinable_simp:                      0
% 2.56/0.99  sim_ac_normalised:                      0
% 2.56/0.99  sim_smt_subsumption:                    0
% 2.56/0.99  
%------------------------------------------------------------------------------
