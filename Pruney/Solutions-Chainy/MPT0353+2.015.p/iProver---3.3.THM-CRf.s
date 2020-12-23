%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:40 EST 2020

% Result     : Theorem 34.76s
% Output     : CNFRefutation 34.76s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 356 expanded)
%              Number of clauses        :   61 ( 145 expanded)
%              Number of leaves         :   12 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  146 ( 727 expanded)
%              Number of equality atoms :   94 ( 351 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k7_subset_1(X0,X1,sK2) != k9_subset_1(X0,X1,k3_subset_1(X0,sK2))
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f24,f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f23,f24,f24,f24])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_96,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_258,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_96])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_102,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | k3_subset_1(X1_38,X0_38) = k4_xboole_0(X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_253,plain,
    ( k3_subset_1(X0_38,X1_38) = k4_xboole_0(X0_38,X1_38)
    | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102])).

cnf(c_440,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_258,c_253])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_101,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | m1_subset_1(k3_subset_1(X1_38,X0_38),k1_zfmisc_1(X1_38)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_254,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(X1_38)) != iProver_top
    | m1_subset_1(k3_subset_1(X1_38,X0_38),k1_zfmisc_1(X1_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_486,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_440,c_254])).

cnf(c_12,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_740,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_12])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_98,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)) = k9_subset_1(X1_38,X2_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_257,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k9_subset_1(X2_38,X0_38,X1_38)
    | m1_subset_1(X1_38,k1_zfmisc_1(X2_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_98])).

cnf(c_1621,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) = k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_740,c_257])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_95,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_259,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_95])).

cnf(c_441,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_259,c_253])).

cnf(c_606,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_441,c_254])).

cnf(c_11,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_749,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_11])).

cnf(c_754,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_749,c_253])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_100,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | k3_subset_1(X1_38,k3_subset_1(X1_38,X0_38)) = X0_38 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_255,plain,
    ( k3_subset_1(X0_38,k3_subset_1(X0_38,X1_38)) = X1_38
    | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_552,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_259,c_255])).

cnf(c_554,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_552,c_441])).

cnf(c_755,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_754,c_554])).

cnf(c_1618,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(superposition,[status(thm)],[c_258,c_257])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_104,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1973,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(superposition,[status(thm)],[c_1618,c_104])).

cnf(c_2,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_103,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X2_38,k4_xboole_0(X2_38,X1_38))) = k4_xboole_0(k5_xboole_0(X0_38,X2_38),k4_xboole_0(k5_xboole_0(X0_38,X2_38),X1_38)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2407,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k9_subset_1(sK0,X1_38,sK2)) = k4_xboole_0(k5_xboole_0(X0_38,sK2),k4_xboole_0(k5_xboole_0(X0_38,sK2),X1_38)) ),
    inference(superposition,[status(thm)],[c_1973,c_103])).

cnf(c_6011,plain,
    ( k4_xboole_0(k5_xboole_0(sK0,sK2),k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_755,c_2407])).

cnf(c_745,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_740,c_253])).

cnf(c_551,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_258,c_255])).

cnf(c_555,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_551,c_440])).

cnf(c_746,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_745,c_555])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_105,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38))) = k4_xboole_0(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_815,plain,
    ( k5_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_746,c_105])).

cnf(c_6079,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_6011,c_815])).

cnf(c_1619,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)) = k9_subset_1(sK0,X0_38,sK1) ),
    inference(superposition,[status(thm)],[c_259,c_257])).

cnf(c_1965,plain,
    ( k5_xboole_0(X0_38,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(X0_38,sK2) ),
    inference(superposition,[status(thm)],[c_1618,c_105])).

cnf(c_6080,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_6079,c_1619,c_1965])).

cnf(c_6893,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_6080,c_104])).

cnf(c_74381,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1621,c_6893])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_99,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | k7_subset_1(X1_38,X0_38,X2_38) = k4_xboole_0(X0_38,X2_38) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_256,plain,
    ( k7_subset_1(X0_38,X1_38,X2_38) = k4_xboole_0(X1_38,X2_38)
    | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_930,plain,
    ( k7_subset_1(sK0,sK1,X0_38) = k4_xboole_0(sK1,X0_38) ),
    inference(superposition,[status(thm)],[c_259,c_256])).

cnf(c_8,negated_conjecture,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_97,negated_conjecture,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_442,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k7_subset_1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_440,c_97])).

cnf(c_1293,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_930,c_442])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74381,c_1293])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 34.76/5.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.76/5.03  
% 34.76/5.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 34.76/5.03  
% 34.76/5.03  ------  iProver source info
% 34.76/5.03  
% 34.76/5.03  git: date: 2020-06-30 10:37:57 +0100
% 34.76/5.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 34.76/5.03  git: non_committed_changes: false
% 34.76/5.03  git: last_make_outside_of_git: false
% 34.76/5.03  
% 34.76/5.03  ------ 
% 34.76/5.03  
% 34.76/5.03  ------ Input Options
% 34.76/5.03  
% 34.76/5.03  --out_options                           all
% 34.76/5.03  --tptp_safe_out                         true
% 34.76/5.03  --problem_path                          ""
% 34.76/5.03  --include_path                          ""
% 34.76/5.03  --clausifier                            res/vclausify_rel
% 34.76/5.03  --clausifier_options                    ""
% 34.76/5.03  --stdin                                 false
% 34.76/5.03  --stats_out                             all
% 34.76/5.03  
% 34.76/5.03  ------ General Options
% 34.76/5.03  
% 34.76/5.03  --fof                                   false
% 34.76/5.03  --time_out_real                         305.
% 34.76/5.03  --time_out_virtual                      -1.
% 34.76/5.03  --symbol_type_check                     false
% 34.76/5.03  --clausify_out                          false
% 34.76/5.03  --sig_cnt_out                           false
% 34.76/5.03  --trig_cnt_out                          false
% 34.76/5.03  --trig_cnt_out_tolerance                1.
% 34.76/5.03  --trig_cnt_out_sk_spl                   false
% 34.76/5.03  --abstr_cl_out                          false
% 34.76/5.03  
% 34.76/5.03  ------ Global Options
% 34.76/5.03  
% 34.76/5.03  --schedule                              default
% 34.76/5.03  --add_important_lit                     false
% 34.76/5.03  --prop_solver_per_cl                    1000
% 34.76/5.03  --min_unsat_core                        false
% 34.76/5.03  --soft_assumptions                      false
% 34.76/5.03  --soft_lemma_size                       3
% 34.76/5.03  --prop_impl_unit_size                   0
% 34.76/5.03  --prop_impl_unit                        []
% 34.76/5.03  --share_sel_clauses                     true
% 34.76/5.03  --reset_solvers                         false
% 34.76/5.03  --bc_imp_inh                            [conj_cone]
% 34.76/5.03  --conj_cone_tolerance                   3.
% 34.76/5.03  --extra_neg_conj                        none
% 34.76/5.03  --large_theory_mode                     true
% 34.76/5.03  --prolific_symb_bound                   200
% 34.76/5.03  --lt_threshold                          2000
% 34.76/5.03  --clause_weak_htbl                      true
% 34.76/5.03  --gc_record_bc_elim                     false
% 34.76/5.03  
% 34.76/5.03  ------ Preprocessing Options
% 34.76/5.03  
% 34.76/5.03  --preprocessing_flag                    true
% 34.76/5.03  --time_out_prep_mult                    0.1
% 34.76/5.03  --splitting_mode                        input
% 34.76/5.03  --splitting_grd                         true
% 34.76/5.03  --splitting_cvd                         false
% 34.76/5.03  --splitting_cvd_svl                     false
% 34.76/5.03  --splitting_nvd                         32
% 34.76/5.03  --sub_typing                            true
% 34.76/5.03  --prep_gs_sim                           true
% 34.76/5.03  --prep_unflatten                        true
% 34.76/5.03  --prep_res_sim                          true
% 34.76/5.03  --prep_upred                            true
% 34.76/5.03  --prep_sem_filter                       exhaustive
% 34.76/5.03  --prep_sem_filter_out                   false
% 34.76/5.03  --pred_elim                             true
% 34.76/5.03  --res_sim_input                         true
% 34.76/5.03  --eq_ax_congr_red                       true
% 34.76/5.03  --pure_diseq_elim                       true
% 34.76/5.03  --brand_transform                       false
% 34.76/5.03  --non_eq_to_eq                          false
% 34.76/5.03  --prep_def_merge                        true
% 34.76/5.03  --prep_def_merge_prop_impl              false
% 34.76/5.03  --prep_def_merge_mbd                    true
% 34.76/5.03  --prep_def_merge_tr_red                 false
% 34.76/5.03  --prep_def_merge_tr_cl                  false
% 34.76/5.03  --smt_preprocessing                     true
% 34.76/5.03  --smt_ac_axioms                         fast
% 34.76/5.03  --preprocessed_out                      false
% 34.76/5.03  --preprocessed_stats                    false
% 34.76/5.03  
% 34.76/5.03  ------ Abstraction refinement Options
% 34.76/5.03  
% 34.76/5.03  --abstr_ref                             []
% 34.76/5.03  --abstr_ref_prep                        false
% 34.76/5.03  --abstr_ref_until_sat                   false
% 34.76/5.03  --abstr_ref_sig_restrict                funpre
% 34.76/5.03  --abstr_ref_af_restrict_to_split_sk     false
% 34.76/5.03  --abstr_ref_under                       []
% 34.76/5.03  
% 34.76/5.03  ------ SAT Options
% 34.76/5.03  
% 34.76/5.03  --sat_mode                              false
% 34.76/5.03  --sat_fm_restart_options                ""
% 34.76/5.03  --sat_gr_def                            false
% 34.76/5.03  --sat_epr_types                         true
% 34.76/5.03  --sat_non_cyclic_types                  false
% 34.76/5.03  --sat_finite_models                     false
% 34.76/5.03  --sat_fm_lemmas                         false
% 34.76/5.03  --sat_fm_prep                           false
% 34.76/5.03  --sat_fm_uc_incr                        true
% 34.76/5.03  --sat_out_model                         small
% 34.76/5.03  --sat_out_clauses                       false
% 34.76/5.03  
% 34.76/5.03  ------ QBF Options
% 34.76/5.03  
% 34.76/5.03  --qbf_mode                              false
% 34.76/5.03  --qbf_elim_univ                         false
% 34.76/5.03  --qbf_dom_inst                          none
% 34.76/5.03  --qbf_dom_pre_inst                      false
% 34.76/5.03  --qbf_sk_in                             false
% 34.76/5.03  --qbf_pred_elim                         true
% 34.76/5.03  --qbf_split                             512
% 34.76/5.03  
% 34.76/5.03  ------ BMC1 Options
% 34.76/5.03  
% 34.76/5.03  --bmc1_incremental                      false
% 34.76/5.03  --bmc1_axioms                           reachable_all
% 34.76/5.03  --bmc1_min_bound                        0
% 34.76/5.03  --bmc1_max_bound                        -1
% 34.76/5.03  --bmc1_max_bound_default                -1
% 34.76/5.03  --bmc1_symbol_reachability              true
% 34.76/5.03  --bmc1_property_lemmas                  false
% 34.76/5.03  --bmc1_k_induction                      false
% 34.76/5.03  --bmc1_non_equiv_states                 false
% 34.76/5.03  --bmc1_deadlock                         false
% 34.76/5.03  --bmc1_ucm                              false
% 34.76/5.03  --bmc1_add_unsat_core                   none
% 34.76/5.03  --bmc1_unsat_core_children              false
% 34.76/5.03  --bmc1_unsat_core_extrapolate_axioms    false
% 34.76/5.03  --bmc1_out_stat                         full
% 34.76/5.03  --bmc1_ground_init                      false
% 34.76/5.03  --bmc1_pre_inst_next_state              false
% 34.76/5.03  --bmc1_pre_inst_state                   false
% 34.76/5.03  --bmc1_pre_inst_reach_state             false
% 34.76/5.03  --bmc1_out_unsat_core                   false
% 34.76/5.03  --bmc1_aig_witness_out                  false
% 34.76/5.03  --bmc1_verbose                          false
% 34.76/5.03  --bmc1_dump_clauses_tptp                false
% 34.76/5.03  --bmc1_dump_unsat_core_tptp             false
% 34.76/5.03  --bmc1_dump_file                        -
% 34.76/5.03  --bmc1_ucm_expand_uc_limit              128
% 34.76/5.03  --bmc1_ucm_n_expand_iterations          6
% 34.76/5.03  --bmc1_ucm_extend_mode                  1
% 34.76/5.03  --bmc1_ucm_init_mode                    2
% 34.76/5.03  --bmc1_ucm_cone_mode                    none
% 34.76/5.03  --bmc1_ucm_reduced_relation_type        0
% 34.76/5.03  --bmc1_ucm_relax_model                  4
% 34.76/5.03  --bmc1_ucm_full_tr_after_sat            true
% 34.76/5.03  --bmc1_ucm_expand_neg_assumptions       false
% 34.76/5.03  --bmc1_ucm_layered_model                none
% 34.76/5.03  --bmc1_ucm_max_lemma_size               10
% 34.76/5.03  
% 34.76/5.03  ------ AIG Options
% 34.76/5.03  
% 34.76/5.03  --aig_mode                              false
% 34.76/5.03  
% 34.76/5.03  ------ Instantiation Options
% 34.76/5.03  
% 34.76/5.03  --instantiation_flag                    true
% 34.76/5.03  --inst_sos_flag                         true
% 34.76/5.03  --inst_sos_phase                        true
% 34.76/5.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 34.76/5.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 34.76/5.03  --inst_lit_sel_side                     num_symb
% 34.76/5.03  --inst_solver_per_active                1400
% 34.76/5.03  --inst_solver_calls_frac                1.
% 34.76/5.03  --inst_passive_queue_type               priority_queues
% 34.76/5.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 34.76/5.03  --inst_passive_queues_freq              [25;2]
% 34.76/5.03  --inst_dismatching                      true
% 34.76/5.03  --inst_eager_unprocessed_to_passive     true
% 34.76/5.03  --inst_prop_sim_given                   true
% 34.76/5.03  --inst_prop_sim_new                     false
% 34.76/5.03  --inst_subs_new                         false
% 34.76/5.03  --inst_eq_res_simp                      false
% 34.76/5.03  --inst_subs_given                       false
% 34.76/5.03  --inst_orphan_elimination               true
% 34.76/5.03  --inst_learning_loop_flag               true
% 34.76/5.03  --inst_learning_start                   3000
% 34.76/5.03  --inst_learning_factor                  2
% 34.76/5.03  --inst_start_prop_sim_after_learn       3
% 34.76/5.03  --inst_sel_renew                        solver
% 34.76/5.03  --inst_lit_activity_flag                true
% 34.76/5.03  --inst_restr_to_given                   false
% 34.76/5.03  --inst_activity_threshold               500
% 34.76/5.03  --inst_out_proof                        true
% 34.76/5.03  
% 34.76/5.03  ------ Resolution Options
% 34.76/5.03  
% 34.76/5.03  --resolution_flag                       true
% 34.76/5.03  --res_lit_sel                           adaptive
% 34.76/5.03  --res_lit_sel_side                      none
% 34.76/5.03  --res_ordering                          kbo
% 34.76/5.03  --res_to_prop_solver                    active
% 34.76/5.03  --res_prop_simpl_new                    false
% 34.76/5.03  --res_prop_simpl_given                  true
% 34.76/5.03  --res_passive_queue_type                priority_queues
% 34.76/5.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 34.76/5.03  --res_passive_queues_freq               [15;5]
% 34.76/5.03  --res_forward_subs                      full
% 34.76/5.03  --res_backward_subs                     full
% 34.76/5.03  --res_forward_subs_resolution           true
% 34.76/5.03  --res_backward_subs_resolution          true
% 34.76/5.03  --res_orphan_elimination                true
% 34.76/5.03  --res_time_limit                        2.
% 34.76/5.03  --res_out_proof                         true
% 34.76/5.03  
% 34.76/5.03  ------ Superposition Options
% 34.76/5.03  
% 34.76/5.03  --superposition_flag                    true
% 34.76/5.03  --sup_passive_queue_type                priority_queues
% 34.76/5.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 34.76/5.03  --sup_passive_queues_freq               [8;1;4]
% 34.76/5.03  --demod_completeness_check              fast
% 34.76/5.03  --demod_use_ground                      true
% 34.76/5.03  --sup_to_prop_solver                    passive
% 34.76/5.03  --sup_prop_simpl_new                    true
% 34.76/5.03  --sup_prop_simpl_given                  true
% 34.76/5.03  --sup_fun_splitting                     true
% 34.76/5.03  --sup_smt_interval                      50000
% 34.76/5.03  
% 34.76/5.03  ------ Superposition Simplification Setup
% 34.76/5.03  
% 34.76/5.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 34.76/5.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 34.76/5.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 34.76/5.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 34.76/5.03  --sup_full_triv                         [TrivRules;PropSubs]
% 34.76/5.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 34.76/5.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 34.76/5.03  --sup_immed_triv                        [TrivRules]
% 34.76/5.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 34.76/5.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.76/5.03  --sup_immed_bw_main                     []
% 34.76/5.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 34.76/5.03  --sup_input_triv                        [Unflattening;TrivRules]
% 34.76/5.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.76/5.03  --sup_input_bw                          []
% 34.76/5.03  
% 34.76/5.03  ------ Combination Options
% 34.76/5.03  
% 34.76/5.03  --comb_res_mult                         3
% 34.76/5.03  --comb_sup_mult                         2
% 34.76/5.03  --comb_inst_mult                        10
% 34.76/5.03  
% 34.76/5.03  ------ Debug Options
% 34.76/5.03  
% 34.76/5.03  --dbg_backtrace                         false
% 34.76/5.03  --dbg_dump_prop_clauses                 false
% 34.76/5.03  --dbg_dump_prop_clauses_file            -
% 34.76/5.03  --dbg_out_stat                          false
% 34.76/5.03  ------ Parsing...
% 34.76/5.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 34.76/5.03  
% 34.76/5.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 34.76/5.03  
% 34.76/5.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 34.76/5.03  
% 34.76/5.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 34.76/5.03  ------ Proving...
% 34.76/5.03  ------ Problem Properties 
% 34.76/5.03  
% 34.76/5.03  
% 34.76/5.03  clauses                                 11
% 34.76/5.03  conjectures                             3
% 34.76/5.03  EPR                                     0
% 34.76/5.03  Horn                                    11
% 34.76/5.03  unary                                   6
% 34.76/5.03  binary                                  5
% 34.76/5.03  lits                                    16
% 34.76/5.03  lits eq                                 8
% 34.76/5.03  fd_pure                                 0
% 34.76/5.03  fd_pseudo                               0
% 34.76/5.03  fd_cond                                 0
% 34.76/5.03  fd_pseudo_cond                          0
% 34.76/5.03  AC symbols                              0
% 34.76/5.03  
% 34.76/5.03  ------ Schedule dynamic 5 is on 
% 34.76/5.03  
% 34.76/5.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 34.76/5.03  
% 34.76/5.03  
% 34.76/5.03  ------ 
% 34.76/5.03  Current options:
% 34.76/5.03  ------ 
% 34.76/5.03  
% 34.76/5.03  ------ Input Options
% 34.76/5.03  
% 34.76/5.03  --out_options                           all
% 34.76/5.03  --tptp_safe_out                         true
% 34.76/5.03  --problem_path                          ""
% 34.76/5.03  --include_path                          ""
% 34.76/5.03  --clausifier                            res/vclausify_rel
% 34.76/5.03  --clausifier_options                    ""
% 34.76/5.03  --stdin                                 false
% 34.76/5.03  --stats_out                             all
% 34.76/5.03  
% 34.76/5.03  ------ General Options
% 34.76/5.03  
% 34.76/5.03  --fof                                   false
% 34.76/5.03  --time_out_real                         305.
% 34.76/5.03  --time_out_virtual                      -1.
% 34.76/5.03  --symbol_type_check                     false
% 34.76/5.03  --clausify_out                          false
% 34.76/5.03  --sig_cnt_out                           false
% 34.76/5.03  --trig_cnt_out                          false
% 34.76/5.03  --trig_cnt_out_tolerance                1.
% 34.76/5.03  --trig_cnt_out_sk_spl                   false
% 34.76/5.03  --abstr_cl_out                          false
% 34.76/5.03  
% 34.76/5.03  ------ Global Options
% 34.76/5.03  
% 34.76/5.03  --schedule                              default
% 34.76/5.03  --add_important_lit                     false
% 34.76/5.03  --prop_solver_per_cl                    1000
% 34.76/5.03  --min_unsat_core                        false
% 34.76/5.03  --soft_assumptions                      false
% 34.76/5.03  --soft_lemma_size                       3
% 34.76/5.03  --prop_impl_unit_size                   0
% 34.76/5.03  --prop_impl_unit                        []
% 34.76/5.03  --share_sel_clauses                     true
% 34.76/5.03  --reset_solvers                         false
% 34.76/5.03  --bc_imp_inh                            [conj_cone]
% 34.76/5.03  --conj_cone_tolerance                   3.
% 34.76/5.03  --extra_neg_conj                        none
% 34.76/5.03  --large_theory_mode                     true
% 34.76/5.03  --prolific_symb_bound                   200
% 34.76/5.03  --lt_threshold                          2000
% 34.76/5.03  --clause_weak_htbl                      true
% 34.76/5.03  --gc_record_bc_elim                     false
% 34.76/5.03  
% 34.76/5.03  ------ Preprocessing Options
% 34.76/5.03  
% 34.76/5.03  --preprocessing_flag                    true
% 34.76/5.03  --time_out_prep_mult                    0.1
% 34.76/5.03  --splitting_mode                        input
% 34.76/5.03  --splitting_grd                         true
% 34.76/5.03  --splitting_cvd                         false
% 34.76/5.03  --splitting_cvd_svl                     false
% 34.76/5.03  --splitting_nvd                         32
% 34.76/5.03  --sub_typing                            true
% 34.76/5.03  --prep_gs_sim                           true
% 34.76/5.03  --prep_unflatten                        true
% 34.76/5.03  --prep_res_sim                          true
% 34.76/5.03  --prep_upred                            true
% 34.76/5.03  --prep_sem_filter                       exhaustive
% 34.76/5.03  --prep_sem_filter_out                   false
% 34.76/5.03  --pred_elim                             true
% 34.76/5.03  --res_sim_input                         true
% 34.76/5.03  --eq_ax_congr_red                       true
% 34.76/5.03  --pure_diseq_elim                       true
% 34.76/5.03  --brand_transform                       false
% 34.76/5.03  --non_eq_to_eq                          false
% 34.76/5.03  --prep_def_merge                        true
% 34.76/5.03  --prep_def_merge_prop_impl              false
% 34.76/5.03  --prep_def_merge_mbd                    true
% 34.76/5.03  --prep_def_merge_tr_red                 false
% 34.76/5.03  --prep_def_merge_tr_cl                  false
% 34.76/5.03  --smt_preprocessing                     true
% 34.76/5.03  --smt_ac_axioms                         fast
% 34.76/5.03  --preprocessed_out                      false
% 34.76/5.03  --preprocessed_stats                    false
% 34.76/5.03  
% 34.76/5.03  ------ Abstraction refinement Options
% 34.76/5.03  
% 34.76/5.03  --abstr_ref                             []
% 34.76/5.03  --abstr_ref_prep                        false
% 34.76/5.03  --abstr_ref_until_sat                   false
% 34.76/5.03  --abstr_ref_sig_restrict                funpre
% 34.76/5.03  --abstr_ref_af_restrict_to_split_sk     false
% 34.76/5.03  --abstr_ref_under                       []
% 34.76/5.03  
% 34.76/5.03  ------ SAT Options
% 34.76/5.03  
% 34.76/5.03  --sat_mode                              false
% 34.76/5.03  --sat_fm_restart_options                ""
% 34.76/5.03  --sat_gr_def                            false
% 34.76/5.03  --sat_epr_types                         true
% 34.76/5.03  --sat_non_cyclic_types                  false
% 34.76/5.03  --sat_finite_models                     false
% 34.76/5.03  --sat_fm_lemmas                         false
% 34.76/5.03  --sat_fm_prep                           false
% 34.76/5.03  --sat_fm_uc_incr                        true
% 34.76/5.03  --sat_out_model                         small
% 34.76/5.03  --sat_out_clauses                       false
% 34.76/5.03  
% 34.76/5.03  ------ QBF Options
% 34.76/5.03  
% 34.76/5.03  --qbf_mode                              false
% 34.76/5.03  --qbf_elim_univ                         false
% 34.76/5.03  --qbf_dom_inst                          none
% 34.76/5.03  --qbf_dom_pre_inst                      false
% 34.76/5.03  --qbf_sk_in                             false
% 34.76/5.03  --qbf_pred_elim                         true
% 34.76/5.03  --qbf_split                             512
% 34.76/5.03  
% 34.76/5.03  ------ BMC1 Options
% 34.76/5.03  
% 34.76/5.03  --bmc1_incremental                      false
% 34.76/5.03  --bmc1_axioms                           reachable_all
% 34.76/5.03  --bmc1_min_bound                        0
% 34.76/5.03  --bmc1_max_bound                        -1
% 34.76/5.03  --bmc1_max_bound_default                -1
% 34.76/5.03  --bmc1_symbol_reachability              true
% 34.76/5.03  --bmc1_property_lemmas                  false
% 34.76/5.03  --bmc1_k_induction                      false
% 34.76/5.03  --bmc1_non_equiv_states                 false
% 34.76/5.03  --bmc1_deadlock                         false
% 34.76/5.03  --bmc1_ucm                              false
% 34.76/5.03  --bmc1_add_unsat_core                   none
% 34.76/5.03  --bmc1_unsat_core_children              false
% 34.76/5.03  --bmc1_unsat_core_extrapolate_axioms    false
% 34.76/5.03  --bmc1_out_stat                         full
% 34.76/5.03  --bmc1_ground_init                      false
% 34.76/5.03  --bmc1_pre_inst_next_state              false
% 34.76/5.03  --bmc1_pre_inst_state                   false
% 34.76/5.03  --bmc1_pre_inst_reach_state             false
% 34.76/5.03  --bmc1_out_unsat_core                   false
% 34.76/5.03  --bmc1_aig_witness_out                  false
% 34.76/5.03  --bmc1_verbose                          false
% 34.76/5.03  --bmc1_dump_clauses_tptp                false
% 34.76/5.03  --bmc1_dump_unsat_core_tptp             false
% 34.76/5.03  --bmc1_dump_file                        -
% 34.76/5.03  --bmc1_ucm_expand_uc_limit              128
% 34.76/5.03  --bmc1_ucm_n_expand_iterations          6
% 34.76/5.03  --bmc1_ucm_extend_mode                  1
% 34.76/5.03  --bmc1_ucm_init_mode                    2
% 34.76/5.03  --bmc1_ucm_cone_mode                    none
% 34.76/5.03  --bmc1_ucm_reduced_relation_type        0
% 34.76/5.03  --bmc1_ucm_relax_model                  4
% 34.76/5.03  --bmc1_ucm_full_tr_after_sat            true
% 34.76/5.03  --bmc1_ucm_expand_neg_assumptions       false
% 34.76/5.03  --bmc1_ucm_layered_model                none
% 34.76/5.03  --bmc1_ucm_max_lemma_size               10
% 34.76/5.03  
% 34.76/5.03  ------ AIG Options
% 34.76/5.03  
% 34.76/5.03  --aig_mode                              false
% 34.76/5.03  
% 34.76/5.03  ------ Instantiation Options
% 34.76/5.03  
% 34.76/5.03  --instantiation_flag                    true
% 34.76/5.03  --inst_sos_flag                         true
% 34.76/5.03  --inst_sos_phase                        true
% 34.76/5.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 34.76/5.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 34.76/5.03  --inst_lit_sel_side                     none
% 34.76/5.03  --inst_solver_per_active                1400
% 34.76/5.03  --inst_solver_calls_frac                1.
% 34.76/5.03  --inst_passive_queue_type               priority_queues
% 34.76/5.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 34.76/5.03  --inst_passive_queues_freq              [25;2]
% 34.76/5.03  --inst_dismatching                      true
% 34.76/5.03  --inst_eager_unprocessed_to_passive     true
% 34.76/5.03  --inst_prop_sim_given                   true
% 34.76/5.03  --inst_prop_sim_new                     false
% 34.76/5.03  --inst_subs_new                         false
% 34.76/5.03  --inst_eq_res_simp                      false
% 34.76/5.03  --inst_subs_given                       false
% 34.76/5.03  --inst_orphan_elimination               true
% 34.76/5.03  --inst_learning_loop_flag               true
% 34.76/5.03  --inst_learning_start                   3000
% 34.76/5.03  --inst_learning_factor                  2
% 34.76/5.03  --inst_start_prop_sim_after_learn       3
% 34.76/5.03  --inst_sel_renew                        solver
% 34.76/5.03  --inst_lit_activity_flag                true
% 34.76/5.03  --inst_restr_to_given                   false
% 34.76/5.03  --inst_activity_threshold               500
% 34.76/5.03  --inst_out_proof                        true
% 34.76/5.03  
% 34.76/5.03  ------ Resolution Options
% 34.76/5.03  
% 34.76/5.03  --resolution_flag                       false
% 34.76/5.03  --res_lit_sel                           adaptive
% 34.76/5.03  --res_lit_sel_side                      none
% 34.76/5.03  --res_ordering                          kbo
% 34.76/5.03  --res_to_prop_solver                    active
% 34.76/5.03  --res_prop_simpl_new                    false
% 34.76/5.03  --res_prop_simpl_given                  true
% 34.76/5.03  --res_passive_queue_type                priority_queues
% 34.76/5.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 34.76/5.03  --res_passive_queues_freq               [15;5]
% 34.76/5.03  --res_forward_subs                      full
% 34.76/5.03  --res_backward_subs                     full
% 34.76/5.03  --res_forward_subs_resolution           true
% 34.76/5.03  --res_backward_subs_resolution          true
% 34.76/5.03  --res_orphan_elimination                true
% 34.76/5.03  --res_time_limit                        2.
% 34.76/5.03  --res_out_proof                         true
% 34.76/5.03  
% 34.76/5.03  ------ Superposition Options
% 34.76/5.03  
% 34.76/5.03  --superposition_flag                    true
% 34.76/5.03  --sup_passive_queue_type                priority_queues
% 34.76/5.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 34.76/5.03  --sup_passive_queues_freq               [8;1;4]
% 34.76/5.03  --demod_completeness_check              fast
% 34.76/5.03  --demod_use_ground                      true
% 34.76/5.03  --sup_to_prop_solver                    passive
% 34.76/5.03  --sup_prop_simpl_new                    true
% 34.76/5.03  --sup_prop_simpl_given                  true
% 34.76/5.03  --sup_fun_splitting                     true
% 34.76/5.03  --sup_smt_interval                      50000
% 34.76/5.03  
% 34.76/5.03  ------ Superposition Simplification Setup
% 34.76/5.03  
% 34.76/5.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 34.76/5.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 34.76/5.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 34.76/5.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 34.76/5.03  --sup_full_triv                         [TrivRules;PropSubs]
% 34.76/5.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 34.76/5.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 34.76/5.03  --sup_immed_triv                        [TrivRules]
% 34.76/5.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 34.76/5.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.76/5.03  --sup_immed_bw_main                     []
% 34.76/5.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 34.76/5.03  --sup_input_triv                        [Unflattening;TrivRules]
% 34.76/5.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.76/5.03  --sup_input_bw                          []
% 34.76/5.03  
% 34.76/5.03  ------ Combination Options
% 34.76/5.03  
% 34.76/5.03  --comb_res_mult                         3
% 34.76/5.03  --comb_sup_mult                         2
% 34.76/5.03  --comb_inst_mult                        10
% 34.76/5.03  
% 34.76/5.03  ------ Debug Options
% 34.76/5.03  
% 34.76/5.03  --dbg_backtrace                         false
% 34.76/5.03  --dbg_dump_prop_clauses                 false
% 34.76/5.03  --dbg_dump_prop_clauses_file            -
% 34.76/5.03  --dbg_out_stat                          false
% 34.76/5.03  
% 34.76/5.03  
% 34.76/5.03  
% 34.76/5.03  
% 34.76/5.03  ------ Proving...
% 34.76/5.03  
% 34.76/5.03  
% 34.76/5.03  % SZS status Theorem for theBenchmark.p
% 34.76/5.03  
% 34.76/5.03  % SZS output start CNFRefutation for theBenchmark.p
% 34.76/5.03  
% 34.76/5.03  fof(f10,conjecture,(
% 34.76/5.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f11,negated_conjecture,(
% 34.76/5.03    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 34.76/5.03    inference(negated_conjecture,[],[f10])).
% 34.76/5.03  
% 34.76/5.03  fof(f17,plain,(
% 34.76/5.03    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.76/5.03    inference(ennf_transformation,[],[f11])).
% 34.76/5.03  
% 34.76/5.03  fof(f19,plain,(
% 34.76/5.03    ( ! [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k7_subset_1(X0,X1,sK2) != k9_subset_1(X0,X1,k3_subset_1(X0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 34.76/5.03    introduced(choice_axiom,[])).
% 34.76/5.03  
% 34.76/5.03  fof(f18,plain,(
% 34.76/5.03    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 34.76/5.03    introduced(choice_axiom,[])).
% 34.76/5.03  
% 34.76/5.03  fof(f20,plain,(
% 34.76/5.03    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 34.76/5.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).
% 34.76/5.03  
% 34.76/5.03  fof(f31,plain,(
% 34.76/5.03    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 34.76/5.03    inference(cnf_transformation,[],[f20])).
% 34.76/5.03  
% 34.76/5.03  fof(f5,axiom,(
% 34.76/5.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f12,plain,(
% 34.76/5.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.76/5.03    inference(ennf_transformation,[],[f5])).
% 34.76/5.03  
% 34.76/5.03  fof(f25,plain,(
% 34.76/5.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.76/5.03    inference(cnf_transformation,[],[f12])).
% 34.76/5.03  
% 34.76/5.03  fof(f6,axiom,(
% 34.76/5.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f13,plain,(
% 34.76/5.03    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.76/5.03    inference(ennf_transformation,[],[f6])).
% 34.76/5.03  
% 34.76/5.03  fof(f26,plain,(
% 34.76/5.03    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.76/5.03    inference(cnf_transformation,[],[f13])).
% 34.76/5.03  
% 34.76/5.03  fof(f9,axiom,(
% 34.76/5.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f16,plain,(
% 34.76/5.03    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 34.76/5.03    inference(ennf_transformation,[],[f9])).
% 34.76/5.03  
% 34.76/5.03  fof(f29,plain,(
% 34.76/5.03    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 34.76/5.03    inference(cnf_transformation,[],[f16])).
% 34.76/5.03  
% 34.76/5.03  fof(f4,axiom,(
% 34.76/5.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f24,plain,(
% 34.76/5.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 34.76/5.03    inference(cnf_transformation,[],[f4])).
% 34.76/5.03  
% 34.76/5.03  fof(f36,plain,(
% 34.76/5.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 34.76/5.03    inference(definition_unfolding,[],[f29,f24])).
% 34.76/5.03  
% 34.76/5.03  fof(f30,plain,(
% 34.76/5.03    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 34.76/5.03    inference(cnf_transformation,[],[f20])).
% 34.76/5.03  
% 34.76/5.03  fof(f7,axiom,(
% 34.76/5.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f14,plain,(
% 34.76/5.03    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.76/5.03    inference(ennf_transformation,[],[f7])).
% 34.76/5.03  
% 34.76/5.03  fof(f27,plain,(
% 34.76/5.03    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.76/5.03    inference(cnf_transformation,[],[f14])).
% 34.76/5.03  
% 34.76/5.03  fof(f1,axiom,(
% 34.76/5.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f21,plain,(
% 34.76/5.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 34.76/5.03    inference(cnf_transformation,[],[f1])).
% 34.76/5.03  
% 34.76/5.03  fof(f34,plain,(
% 34.76/5.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 34.76/5.03    inference(definition_unfolding,[],[f21,f24,f24])).
% 34.76/5.03  
% 34.76/5.03  fof(f3,axiom,(
% 34.76/5.03    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f23,plain,(
% 34.76/5.03    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 34.76/5.03    inference(cnf_transformation,[],[f3])).
% 34.76/5.03  
% 34.76/5.03  fof(f35,plain,(
% 34.76/5.03    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 34.76/5.03    inference(definition_unfolding,[],[f23,f24,f24,f24])).
% 34.76/5.03  
% 34.76/5.03  fof(f2,axiom,(
% 34.76/5.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f22,plain,(
% 34.76/5.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 34.76/5.03    inference(cnf_transformation,[],[f2])).
% 34.76/5.03  
% 34.76/5.03  fof(f33,plain,(
% 34.76/5.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 34.76/5.03    inference(definition_unfolding,[],[f22,f24])).
% 34.76/5.03  
% 34.76/5.03  fof(f8,axiom,(
% 34.76/5.03    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 34.76/5.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.76/5.03  
% 34.76/5.03  fof(f15,plain,(
% 34.76/5.03    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.76/5.03    inference(ennf_transformation,[],[f8])).
% 34.76/5.03  
% 34.76/5.03  fof(f28,plain,(
% 34.76/5.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.76/5.03    inference(cnf_transformation,[],[f15])).
% 34.76/5.03  
% 34.76/5.03  fof(f32,plain,(
% 34.76/5.03    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 34.76/5.03    inference(cnf_transformation,[],[f20])).
% 34.76/5.03  
% 34.76/5.03  cnf(c_9,negated_conjecture,
% 34.76/5.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 34.76/5.03      inference(cnf_transformation,[],[f31]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_96,negated_conjecture,
% 34.76/5.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_9]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_258,plain,
% 34.76/5.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_96]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_3,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 34.76/5.03      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 34.76/5.03      inference(cnf_transformation,[],[f25]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_102,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 34.76/5.03      | k3_subset_1(X1_38,X0_38) = k4_xboole_0(X1_38,X0_38) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_3]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_253,plain,
% 34.76/5.03      ( k3_subset_1(X0_38,X1_38) = k4_xboole_0(X0_38,X1_38)
% 34.76/5.03      | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_102]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_440,plain,
% 34.76/5.03      ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_258,c_253]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_4,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 34.76/5.03      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 34.76/5.03      inference(cnf_transformation,[],[f26]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_101,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 34.76/5.03      | m1_subset_1(k3_subset_1(X1_38,X0_38),k1_zfmisc_1(X1_38)) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_4]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_254,plain,
% 34.76/5.03      ( m1_subset_1(X0_38,k1_zfmisc_1(X1_38)) != iProver_top
% 34.76/5.03      | m1_subset_1(k3_subset_1(X1_38,X0_38),k1_zfmisc_1(X1_38)) = iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_486,plain,
% 34.76/5.03      ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
% 34.76/5.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_440,c_254]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_12,plain,
% 34.76/5.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_740,plain,
% 34.76/5.03      ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 34.76/5.03      inference(global_propositional_subsumption,
% 34.76/5.03                [status(thm)],
% 34.76/5.03                [c_486,c_12]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_7,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 34.76/5.03      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 34.76/5.03      inference(cnf_transformation,[],[f36]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_98,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 34.76/5.03      | k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)) = k9_subset_1(X1_38,X2_38,X0_38) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_7]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_257,plain,
% 34.76/5.03      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k9_subset_1(X2_38,X0_38,X1_38)
% 34.76/5.03      | m1_subset_1(X1_38,k1_zfmisc_1(X2_38)) != iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_98]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_1621,plain,
% 34.76/5.03      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) = k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_740,c_257]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_10,negated_conjecture,
% 34.76/5.03      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 34.76/5.03      inference(cnf_transformation,[],[f30]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_95,negated_conjecture,
% 34.76/5.03      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_10]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_259,plain,
% 34.76/5.03      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_95]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_441,plain,
% 34.76/5.03      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_259,c_253]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_606,plain,
% 34.76/5.03      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 34.76/5.03      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_441,c_254]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_11,plain,
% 34.76/5.03      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_749,plain,
% 34.76/5.03      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 34.76/5.03      inference(global_propositional_subsumption,
% 34.76/5.03                [status(thm)],
% 34.76/5.03                [c_606,c_11]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_754,plain,
% 34.76/5.03      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_749,c_253]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_5,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 34.76/5.03      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 34.76/5.03      inference(cnf_transformation,[],[f27]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_100,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 34.76/5.03      | k3_subset_1(X1_38,k3_subset_1(X1_38,X0_38)) = X0_38 ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_5]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_255,plain,
% 34.76/5.03      ( k3_subset_1(X0_38,k3_subset_1(X0_38,X1_38)) = X1_38
% 34.76/5.03      | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_100]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_552,plain,
% 34.76/5.03      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_259,c_255]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_554,plain,
% 34.76/5.03      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 34.76/5.03      inference(light_normalisation,[status(thm)],[c_552,c_441]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_755,plain,
% 34.76/5.03      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 34.76/5.03      inference(light_normalisation,[status(thm)],[c_754,c_554]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_1618,plain,
% 34.76/5.03      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) = k9_subset_1(sK0,X0_38,sK2) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_258,c_257]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_1,plain,
% 34.76/5.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 34.76/5.03      inference(cnf_transformation,[],[f34]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_104,plain,
% 34.76/5.03      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_1]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_1973,plain,
% 34.76/5.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_1618,c_104]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_2,plain,
% 34.76/5.03      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
% 34.76/5.03      inference(cnf_transformation,[],[f35]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_103,plain,
% 34.76/5.03      ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X2_38,k4_xboole_0(X2_38,X1_38))) = k4_xboole_0(k5_xboole_0(X0_38,X2_38),k4_xboole_0(k5_xboole_0(X0_38,X2_38),X1_38)) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_2]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_2407,plain,
% 34.76/5.03      ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k9_subset_1(sK0,X1_38,sK2)) = k4_xboole_0(k5_xboole_0(X0_38,sK2),k4_xboole_0(k5_xboole_0(X0_38,sK2),X1_38)) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_1973,c_103]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_6011,plain,
% 34.76/5.03      ( k4_xboole_0(k5_xboole_0(sK0,sK2),k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_755,c_2407]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_745,plain,
% 34.76/5.03      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_740,c_253]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_551,plain,
% 34.76/5.03      ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_258,c_255]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_555,plain,
% 34.76/5.03      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
% 34.76/5.03      inference(light_normalisation,[status(thm)],[c_551,c_440]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_746,plain,
% 34.76/5.03      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
% 34.76/5.03      inference(light_normalisation,[status(thm)],[c_745,c_555]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_0,plain,
% 34.76/5.03      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 34.76/5.03      inference(cnf_transformation,[],[f33]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_105,plain,
% 34.76/5.03      ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38))) = k4_xboole_0(X0_38,X1_38) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_0]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_815,plain,
% 34.76/5.03      ( k5_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_746,c_105]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_6079,plain,
% 34.76/5.03      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(sK1,k9_subset_1(sK0,sK1,sK2)) ),
% 34.76/5.03      inference(light_normalisation,[status(thm)],[c_6011,c_815]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_1619,plain,
% 34.76/5.03      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)) = k9_subset_1(sK0,X0_38,sK1) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_259,c_257]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_1965,plain,
% 34.76/5.03      ( k5_xboole_0(X0_38,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(X0_38,sK2) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_1618,c_105]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_6080,plain,
% 34.76/5.03      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k4_xboole_0(sK1,sK2) ),
% 34.76/5.03      inference(demodulation,[status(thm)],[c_6079,c_1619,c_1965]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_6893,plain,
% 34.76/5.03      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,sK2) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_6080,c_104]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_74381,plain,
% 34.76/5.03      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_1621,c_6893]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_6,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 34.76/5.03      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 34.76/5.03      inference(cnf_transformation,[],[f28]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_99,plain,
% 34.76/5.03      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 34.76/5.03      | k7_subset_1(X1_38,X0_38,X2_38) = k4_xboole_0(X0_38,X2_38) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_6]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_256,plain,
% 34.76/5.03      ( k7_subset_1(X0_38,X1_38,X2_38) = k4_xboole_0(X1_38,X2_38)
% 34.76/5.03      | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
% 34.76/5.03      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_930,plain,
% 34.76/5.03      ( k7_subset_1(sK0,sK1,X0_38) = k4_xboole_0(sK1,X0_38) ),
% 34.76/5.03      inference(superposition,[status(thm)],[c_259,c_256]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_8,negated_conjecture,
% 34.76/5.03      ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
% 34.76/5.03      inference(cnf_transformation,[],[f32]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_97,negated_conjecture,
% 34.76/5.03      ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
% 34.76/5.03      inference(subtyping,[status(esa)],[c_8]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_442,plain,
% 34.76/5.03      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k7_subset_1(sK0,sK1,sK2) ),
% 34.76/5.03      inference(demodulation,[status(thm)],[c_440,c_97]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(c_1293,plain,
% 34.76/5.03      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) ),
% 34.76/5.03      inference(demodulation,[status(thm)],[c_930,c_442]) ).
% 34.76/5.03  
% 34.76/5.03  cnf(contradiction,plain,
% 34.76/5.03      ( $false ),
% 34.76/5.03      inference(minisat,[status(thm)],[c_74381,c_1293]) ).
% 34.76/5.03  
% 34.76/5.03  
% 34.76/5.03  % SZS output end CNFRefutation for theBenchmark.p
% 34.76/5.03  
% 34.76/5.03  ------                               Statistics
% 34.76/5.03  
% 34.76/5.03  ------ General
% 34.76/5.03  
% 34.76/5.03  abstr_ref_over_cycles:                  0
% 34.76/5.03  abstr_ref_under_cycles:                 0
% 34.76/5.03  gc_basic_clause_elim:                   0
% 34.76/5.03  forced_gc_time:                         0
% 34.76/5.03  parsing_time:                           0.007
% 34.76/5.03  unif_index_cands_time:                  0.
% 34.76/5.03  unif_index_add_time:                    0.
% 34.76/5.03  orderings_time:                         0.
% 34.76/5.03  out_proof_time:                         0.011
% 34.76/5.03  total_time:                             4.245
% 34.76/5.03  num_of_symbols:                         43
% 34.76/5.03  num_of_terms:                           187040
% 34.76/5.03  
% 34.76/5.03  ------ Preprocessing
% 34.76/5.03  
% 34.76/5.03  num_of_splits:                          0
% 34.76/5.03  num_of_split_atoms:                     0
% 34.76/5.03  num_of_reused_defs:                     0
% 34.76/5.03  num_eq_ax_congr_red:                    0
% 34.76/5.03  num_of_sem_filtered_clauses:            1
% 34.76/5.03  num_of_subtypes:                        2
% 34.76/5.03  monotx_restored_types:                  0
% 34.76/5.03  sat_num_of_epr_types:                   0
% 34.76/5.03  sat_num_of_non_cyclic_types:            0
% 34.76/5.03  sat_guarded_non_collapsed_types:        1
% 34.76/5.03  num_pure_diseq_elim:                    0
% 34.76/5.03  simp_replaced_by:                       0
% 34.76/5.03  res_preprocessed:                       54
% 34.76/5.03  prep_upred:                             0
% 34.76/5.03  prep_unflattend:                        0
% 34.76/5.03  smt_new_axioms:                         0
% 34.76/5.03  pred_elim_cands:                        1
% 34.76/5.03  pred_elim:                              0
% 34.76/5.03  pred_elim_cl:                           0
% 34.76/5.03  pred_elim_cycles:                       1
% 34.76/5.03  merged_defs:                            0
% 34.76/5.03  merged_defs_ncl:                        0
% 34.76/5.03  bin_hyper_res:                          0
% 34.76/5.03  prep_cycles:                            3
% 34.76/5.03  pred_elim_time:                         0.
% 34.76/5.03  splitting_time:                         0.
% 34.76/5.03  sem_filter_time:                        0.
% 34.76/5.03  monotx_time:                            0.
% 34.76/5.03  subtype_inf_time:                       0.
% 34.76/5.03  
% 34.76/5.03  ------ Problem properties
% 34.76/5.03  
% 34.76/5.03  clauses:                                11
% 34.76/5.03  conjectures:                            3
% 34.76/5.03  epr:                                    0
% 34.76/5.03  horn:                                   11
% 34.76/5.03  ground:                                 3
% 34.76/5.03  unary:                                  6
% 34.76/5.03  binary:                                 5
% 34.76/5.03  lits:                                   16
% 34.76/5.03  lits_eq:                                8
% 34.76/5.03  fd_pure:                                0
% 34.76/5.03  fd_pseudo:                              0
% 34.76/5.03  fd_cond:                                0
% 34.76/5.03  fd_pseudo_cond:                         0
% 34.76/5.03  ac_symbols:                             0
% 34.76/5.03  
% 34.76/5.03  ------ Propositional Solver
% 34.76/5.03  
% 34.76/5.03  prop_solver_calls:                      35
% 34.76/5.03  prop_fast_solver_calls:                 646
% 34.76/5.03  smt_solver_calls:                       0
% 34.76/5.03  smt_fast_solver_calls:                  0
% 34.76/5.03  prop_num_of_clauses:                    28779
% 34.76/5.03  prop_preprocess_simplified:             14384
% 34.76/5.03  prop_fo_subsumed:                       2
% 34.76/5.03  prop_solver_time:                       0.
% 34.76/5.03  smt_solver_time:                        0.
% 34.76/5.03  smt_fast_solver_time:                   0.
% 34.76/5.03  prop_fast_solver_time:                  0.
% 34.76/5.03  prop_unsat_core_time:                   0.002
% 34.76/5.03  
% 34.76/5.03  ------ QBF
% 34.76/5.03  
% 34.76/5.03  qbf_q_res:                              0
% 34.76/5.03  qbf_num_tautologies:                    0
% 34.76/5.03  qbf_prep_cycles:                        0
% 34.76/5.03  
% 34.76/5.03  ------ BMC1
% 34.76/5.03  
% 34.76/5.03  bmc1_current_bound:                     -1
% 34.76/5.03  bmc1_last_solved_bound:                 -1
% 34.76/5.03  bmc1_unsat_core_size:                   -1
% 34.76/5.03  bmc1_unsat_core_parents_size:           -1
% 34.76/5.03  bmc1_merge_next_fun:                    0
% 34.76/5.03  bmc1_unsat_core_clauses_time:           0.
% 34.76/5.03  
% 34.76/5.03  ------ Instantiation
% 34.76/5.03  
% 34.76/5.03  inst_num_of_clauses:                    3706
% 34.76/5.03  inst_num_in_passive:                    1413
% 34.76/5.03  inst_num_in_active:                     1747
% 34.76/5.03  inst_num_in_unprocessed:                546
% 34.76/5.03  inst_num_of_loops:                      1790
% 34.76/5.03  inst_num_of_learning_restarts:          0
% 34.76/5.03  inst_num_moves_active_passive:          35
% 34.76/5.03  inst_lit_activity:                      0
% 34.76/5.03  inst_lit_activity_moves:                0
% 34.76/5.03  inst_num_tautologies:                   0
% 34.76/5.03  inst_num_prop_implied:                  0
% 34.76/5.03  inst_num_existing_simplified:           0
% 34.76/5.03  inst_num_eq_res_simplified:             0
% 34.76/5.03  inst_num_child_elim:                    0
% 34.76/5.03  inst_num_of_dismatching_blockings:      1844
% 34.76/5.03  inst_num_of_non_proper_insts:           6462
% 34.76/5.03  inst_num_of_duplicates:                 0
% 34.76/5.03  inst_inst_num_from_inst_to_res:         0
% 34.76/5.03  inst_dismatching_checking_time:         0.
% 34.76/5.03  
% 34.76/5.03  ------ Resolution
% 34.76/5.03  
% 34.76/5.03  res_num_of_clauses:                     0
% 34.76/5.03  res_num_in_passive:                     0
% 34.76/5.03  res_num_in_active:                      0
% 34.76/5.03  res_num_of_loops:                       57
% 34.76/5.03  res_forward_subset_subsumed:            870
% 34.76/5.03  res_backward_subset_subsumed:           0
% 34.76/5.03  res_forward_subsumed:                   0
% 34.76/5.03  res_backward_subsumed:                  0
% 34.76/5.03  res_forward_subsumption_resolution:     0
% 34.76/5.03  res_backward_subsumption_resolution:    0
% 34.76/5.03  res_clause_to_clause_subsumption:       117944
% 34.76/5.03  res_orphan_elimination:                 0
% 34.76/5.03  res_tautology_del:                      536
% 34.76/5.03  res_num_eq_res_simplified:              0
% 34.76/5.03  res_num_sel_changes:                    0
% 34.76/5.03  res_moves_from_active_to_pass:          0
% 34.76/5.03  
% 34.76/5.03  ------ Superposition
% 34.76/5.03  
% 34.76/5.03  sup_time_total:                         0.
% 34.76/5.03  sup_time_generating:                    0.
% 34.76/5.03  sup_time_sim_full:                      0.
% 34.76/5.03  sup_time_sim_immed:                     0.
% 34.76/5.03  
% 34.76/5.03  sup_num_of_clauses:                     11759
% 34.76/5.03  sup_num_in_active:                      345
% 34.76/5.03  sup_num_in_passive:                     11414
% 34.76/5.03  sup_num_of_loops:                       357
% 34.76/5.03  sup_fw_superposition:                   12990
% 34.76/5.03  sup_bw_superposition:                   10768
% 34.76/5.03  sup_immediate_simplified:               14257
% 34.76/5.03  sup_given_eliminated:                   11
% 34.76/5.03  comparisons_done:                       0
% 34.76/5.03  comparisons_avoided:                    0
% 34.76/5.03  
% 34.76/5.03  ------ Simplifications
% 34.76/5.03  
% 34.76/5.03  
% 34.76/5.03  sim_fw_subset_subsumed:                 2
% 34.76/5.03  sim_bw_subset_subsumed:                 0
% 34.76/5.03  sim_fw_subsumed:                        2241
% 34.76/5.03  sim_bw_subsumed:                        371
% 34.76/5.03  sim_fw_subsumption_res:                 0
% 34.76/5.03  sim_bw_subsumption_res:                 0
% 34.76/5.03  sim_tautology_del:                      0
% 34.76/5.03  sim_eq_tautology_del:                   2711
% 34.76/5.03  sim_eq_res_simp:                        0
% 34.76/5.03  sim_fw_demodulated:                     8123
% 34.76/5.03  sim_bw_demodulated:                     389
% 34.76/5.03  sim_light_normalised:                   8149
% 34.76/5.03  sim_joinable_taut:                      0
% 34.76/5.03  sim_joinable_simp:                      0
% 34.76/5.03  sim_ac_normalised:                      0
% 34.76/5.03  sim_smt_subsumption:                    0
% 34.76/5.03  
%------------------------------------------------------------------------------
