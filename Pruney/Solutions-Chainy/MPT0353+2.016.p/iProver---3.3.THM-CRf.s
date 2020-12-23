%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:40 EST 2020

% Result     : Theorem 55.11s
% Output     : CNFRefutation 55.11s
% Verified   : 
% Statistics : Number of formulae       :  301 (28432 expanded)
%              Number of clauses        :  262 (10696 expanded)
%              Number of leaves         :   13 (7229 expanded)
%              Depth                    :   35
%              Number of atoms          :  350 (48568 expanded)
%              Number of equality atoms :  298 (28123 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( k7_subset_1(X0,X1,sK2) != k9_subset_1(X0,X1,k3_subset_1(X0,sK2))
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
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

fof(f21,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20,f19])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f25,f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f25,f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f24,f25,f25,f25,f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f31,f25])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_98,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_262,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_98])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_104,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | k3_subset_1(X1_38,X0_38) = k4_xboole_0(X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_257,plain,
    ( k3_subset_1(X0_38,X1_38) = k4_xboole_0(X0_38,X1_38)
    | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_476,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_262,c_257])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_103,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | m1_subset_1(k3_subset_1(X1_38,X0_38),k1_zfmisc_1(X1_38)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_258,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(X1_38)) != iProver_top
    | m1_subset_1(k3_subset_1(X1_38,X0_38),k1_zfmisc_1(X1_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_784,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_258])).

cnf(c_13,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_974,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_13])).

cnf(c_979,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_974,c_257])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_102,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | k3_subset_1(X1_38,k3_subset_1(X1_38,X0_38)) = X0_38 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_259,plain,
    ( k3_subset_1(X0_38,k3_subset_1(X0_38,X1_38)) = X1_38
    | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102])).

cnf(c_526,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_262,c_259])).

cnf(c_530,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_526,c_476])).

cnf(c_980,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_979,c_530])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_97,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_263,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_97])).

cnf(c_477,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_263,c_257])).

cnf(c_855,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_477,c_258])).

cnf(c_12,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_983,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_855,c_12])).

cnf(c_988,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_983,c_257])).

cnf(c_527,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_263,c_259])).

cnf(c_529,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_527,c_477])).

cnf(c_989,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_988,c_529])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_107,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_105,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X2_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_449,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)),X2_38) ),
    inference(superposition,[status(thm)],[c_107,c_105])).

cnf(c_633,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X2_38)),X3_38) = k4_xboole_0(X2_38,k4_xboole_0(X2_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X3_38))))) ),
    inference(superposition,[status(thm)],[c_449,c_449])).

cnf(c_2,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_106,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X2_38)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38)))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_264,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38)))) ),
    inference(light_normalisation,[status(thm)],[c_106,c_105])).

cnf(c_662,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38)))),X3_38) = k4_xboole_0(X2_38,k4_xboole_0(X2_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X3_38))))) ),
    inference(light_normalisation,[status(thm)],[c_633,c_105,c_264])).

cnf(c_102041,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)))) ),
    inference(superposition,[status(thm)],[c_989,c_662])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_100,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)) = k9_subset_1(X1_38,X2_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_261,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k9_subset_1(X2_38,X0_38,X1_38)
    | m1_subset_1(X1_38,k1_zfmisc_1(X2_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_1861,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)) = k9_subset_1(sK0,X0_38,sK1) ),
    inference(superposition,[status(thm)],[c_263,c_261])).

cnf(c_104209,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_102041,c_1861])).

cnf(c_107429,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k9_subset_1(sK0,sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_980,c_104209])).

cnf(c_2563,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,sK1)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK1))) ),
    inference(superposition,[status(thm)],[c_1861,c_449])).

cnf(c_107823,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,sK1)) ),
    inference(superposition,[status(thm)],[c_104209,c_2563])).

cnf(c_642,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38))) ),
    inference(superposition,[status(thm)],[c_449,c_105])).

cnf(c_2562,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK1)))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK1))) ),
    inference(superposition,[status(thm)],[c_1861,c_642])).

cnf(c_107824,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK1)))) ),
    inference(superposition,[status(thm)],[c_104209,c_2562])).

cnf(c_611,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X2_38) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) ),
    inference(superposition,[status(thm)],[c_107,c_449])).

cnf(c_2571,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK1,X1_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38) ),
    inference(superposition,[status(thm)],[c_1861,c_611])).

cnf(c_1218,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38)))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)))) ),
    inference(superposition,[status(thm)],[c_107,c_642])).

cnf(c_6857,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK1)))) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK1,X0_38)) ),
    inference(superposition,[status(thm)],[c_2571,c_1218])).

cnf(c_107861,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK1,X0_38)) ),
    inference(light_normalisation,[status(thm)],[c_107824,c_6857])).

cnf(c_624,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X2_38,X3_38))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X2_38)),X1_38),X3_38) ),
    inference(superposition,[status(thm)],[c_449,c_449])).

cnf(c_627,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),X2_38)) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X2_38)),X1_38) ),
    inference(superposition,[status(thm)],[c_449,c_107])).

cnf(c_667,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),X2_38)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,X1_38))) ),
    inference(demodulation,[status(thm)],[c_627,c_105])).

cnf(c_671,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X3_38),X2_38) ),
    inference(demodulation,[status(thm)],[c_624,c_667])).

cnf(c_672,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X3_38),X2_38))) ),
    inference(demodulation,[status(thm)],[c_671,c_105])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_108,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38))) = k4_xboole_0(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3817,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38)))) = k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X3_38),X2_38)) ),
    inference(superposition,[status(thm)],[c_672,c_108])).

cnf(c_13154,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38)) = k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X3_38),X2_38)) ),
    inference(superposition,[status(thm)],[c_3817,c_108])).

cnf(c_17091,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38)) = k4_xboole_0(X2_38,k4_xboole_0(X2_38,k4_xboole_0(X0_38,X1_38))) ),
    inference(superposition,[status(thm)],[c_13154,c_107])).

cnf(c_21708,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,X0_38),k4_xboole_0(sK0,sK1))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)) ),
    inference(superposition,[status(thm)],[c_989,c_17091])).

cnf(c_22210,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0_38),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,X0_38,sK1) ),
    inference(light_normalisation,[status(thm)],[c_21708,c_989,c_1861])).

cnf(c_23151,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,k4_xboole_0(sK0,X0_38),sK1) ),
    inference(superposition,[status(thm)],[c_107,c_22210])).

cnf(c_2591,plain,
    ( k9_subset_1(sK0,sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1861,c_989])).

cnf(c_2589,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK1,X1_38))) = k9_subset_1(sK0,k4_xboole_0(X0_38,X1_38),sK1) ),
    inference(superposition,[status(thm)],[c_1861,c_667])).

cnf(c_2596,plain,
    ( k9_subset_1(sK0,k4_xboole_0(X0_38,X1_38),sK1) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38) ),
    inference(demodulation,[status(thm)],[c_2571,c_2589])).

cnf(c_23309,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) = k4_xboole_0(sK1,X0_38) ),
    inference(demodulation,[status(thm)],[c_23151,c_611,c_2591,c_2596])).

cnf(c_23310,plain,
    ( k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK1)) = k4_xboole_0(sK1,X0_38) ),
    inference(light_normalisation,[status(thm)],[c_23309,c_989,c_1861])).

cnf(c_602,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,X2_38)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)))) ),
    inference(superposition,[status(thm)],[c_107,c_449])).

cnf(c_3238,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X1_38,X2_38)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X1_38)))) ),
    inference(superposition,[status(thm)],[c_107,c_602])).

cnf(c_23396,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0_38)),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK1))))) ),
    inference(superposition,[status(thm)],[c_23310,c_3238])).

cnf(c_2582,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0_38)) = k9_subset_1(sK0,X0_38,sK1) ),
    inference(superposition,[status(thm)],[c_1861,c_107])).

cnf(c_3108,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1_38,k4_xboole_0(sK1,X0_38)))) ),
    inference(superposition,[status(thm)],[c_2582,c_667])).

cnf(c_3142,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) = k9_subset_1(sK0,k4_xboole_0(X1_38,k4_xboole_0(sK1,X0_38)),sK1) ),
    inference(demodulation,[status(thm)],[c_3108,c_2582])).

cnf(c_3143,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK1,X0_38)) ),
    inference(demodulation,[status(thm)],[c_3142,c_2596])).

cnf(c_23431,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK1))))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(sK1,X1_38)) ),
    inference(light_normalisation,[status(thm)],[c_23396,c_2582,c_3143])).

cnf(c_2579,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0_38,X1_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38) ),
    inference(superposition,[status(thm)],[c_1861,c_449])).

cnf(c_23163,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,sK0)))),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,X1_38))),sK1) ),
    inference(superposition,[status(thm)],[c_1218,c_22210])).

cnf(c_381,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38))) = k4_xboole_0(X0_38,X1_38) ),
    inference(superposition,[status(thm)],[c_107,c_108])).

cnf(c_626,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X2_38)),X1_38)) = k4_xboole_0(k4_xboole_0(X0_38,X1_38),X2_38) ),
    inference(superposition,[status(thm)],[c_449,c_381])).

cnf(c_668,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,X1_38)))) = k4_xboole_0(k4_xboole_0(X0_38,X1_38),X2_38) ),
    inference(demodulation,[status(thm)],[c_626,c_105])).

cnf(c_6346,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38)))),k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X3_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38))))))) = k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)))),X3_38) ),
    inference(superposition,[status(thm)],[c_1218,c_668])).

cnf(c_3381,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,X2_38)),k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X3_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38))))))) = k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)))),X3_38) ),
    inference(superposition,[status(thm)],[c_602,c_668])).

cnf(c_2038,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))),k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(X3_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38)),X3_38) ),
    inference(superposition,[status(thm)],[c_667,c_668])).

cnf(c_2091,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X3_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38)),X2_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X3_38),X2_38))) ),
    inference(demodulation,[status(thm)],[c_2038,c_611,c_667])).

cnf(c_1970,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))),k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))),X3_38)) = k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(X3_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38)))) ),
    inference(superposition,[status(thm)],[c_667,c_667])).

cnf(c_2001,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X3_38)),X2_38))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,k4_xboole_0(X3_38,X2_38))))) ),
    inference(demodulation,[status(thm)],[c_1970,c_667])).

cnf(c_2092,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X3_38))),X2_38) ),
    inference(demodulation,[status(thm)],[c_2091,c_668,c_2001])).

cnf(c_3455,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38)))),k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X3_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38))))))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(k4_xboole_0(X2_38,X3_38),k4_xboole_0(X2_38,X0_38)))) ),
    inference(demodulation,[status(thm)],[c_3381,c_611,c_2092])).

cnf(c_6445,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),k4_xboole_0(X1_38,X3_38)))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X3_38)))),X2_38) ),
    inference(light_normalisation,[status(thm)],[c_6346,c_3455])).

cnf(c_3713,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),k4_xboole_0(X1_38,X3_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X3_38,X2_38))))) ),
    inference(superposition,[status(thm)],[c_611,c_672])).

cnf(c_6446,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38)))),X3_38) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,X3_38))))) ),
    inference(demodulation,[status(thm)],[c_6445,c_2092,c_3713])).

cnf(c_23294,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))))) = k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(sK0,X1_38))) ),
    inference(demodulation,[status(thm)],[c_23163,c_2591,c_2596,c_6446])).

cnf(c_23295,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,sK1))))) = k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(sK0,X1_38))) ),
    inference(light_normalisation,[status(thm)],[c_23294,c_989])).

cnf(c_23296,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(sK0,X1_38))) ),
    inference(demodulation,[status(thm)],[c_23295,c_1861])).

cnf(c_23432,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(sK0,X1_38)) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(sK1,X1_38)) ),
    inference(demodulation,[status(thm)],[c_23431,c_2579,c_23296])).

cnf(c_1567,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),k4_xboole_0(sK0,sK1)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)) ),
    inference(superposition,[status(thm)],[c_989,c_449])).

cnf(c_100043,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),k4_xboole_0(sK0,sK1)) = k9_subset_1(sK0,X0_38,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1567,c_1861])).

cnf(c_107862,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK0,X0_38)) ),
    inference(demodulation,[status(thm)],[c_107861,c_23432,c_100043])).

cnf(c_107863,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,sK1)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK0,X0_38)) ),
    inference(demodulation,[status(thm)],[c_107823,c_107862])).

cnf(c_108771,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k9_subset_1(sK0,sK0,sK1))) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK0,sK0)) ),
    inference(demodulation,[status(thm)],[c_107429,c_107863])).

cnf(c_1860,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(superposition,[status(thm)],[c_262,c_261])).

cnf(c_23166,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k9_subset_1(sK0,sK0,sK2),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1860,c_22210])).

cnf(c_9201,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) ),
    inference(superposition,[status(thm)],[c_980,c_3238])).

cnf(c_2436,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(superposition,[status(thm)],[c_1860,c_107])).

cnf(c_9751,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2))) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_9201,c_1860,c_2436])).

cnf(c_23175,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_9751,c_22210])).

cnf(c_23274,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK2)) ),
    inference(demodulation,[status(thm)],[c_23175,c_2591,c_2596])).

cnf(c_23288,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK1,k9_subset_1(sK0,sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_23166,c_23274])).

cnf(c_2445,plain,
    ( k9_subset_1(sK0,sK0,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1860,c_980])).

cnf(c_23289,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_23288,c_2445])).

cnf(c_108772,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_108771,c_2591,c_23289])).

cnf(c_2422,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X0_38,sK2),X1_38))) = k4_xboole_0(k4_xboole_0(X0_38,k9_subset_1(sK0,X0_38,sK2)),X1_38) ),
    inference(superposition,[status(thm)],[c_1860,c_611])).

cnf(c_2417,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,sK2)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK2))) ),
    inference(superposition,[status(thm)],[c_1860,c_449])).

cnf(c_2425,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK2,X1_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),X1_38) ),
    inference(superposition,[status(thm)],[c_1860,c_611])).

cnf(c_18893,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,sK2,sK2)))) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)),sK2),sK2) ),
    inference(superposition,[status(thm)],[c_2417,c_2425])).

cnf(c_1076,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),k4_xboole_0(sK0,sK2)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) ),
    inference(superposition,[status(thm)],[c_980,c_449])).

cnf(c_11612,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1076,c_1860])).

cnf(c_13099,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,X1_38))) = k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK2)))) ),
    inference(superposition,[status(thm)],[c_11612,c_3817])).

cnf(c_13221,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK2)))) = k4_xboole_0(X0_38,k4_xboole_0(sK2,k4_xboole_0(sK0,X1_38))) ),
    inference(light_normalisation,[status(thm)],[c_13099,c_980])).

cnf(c_13222,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(sK2,k4_xboole_0(sK0,X1_38))) = k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK2)) ),
    inference(demodulation,[status(thm)],[c_13221,c_108])).

cnf(c_2416,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK2)))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK2))) ),
    inference(superposition,[status(thm)],[c_1860,c_642])).

cnf(c_16446,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_13222,c_2416])).

cnf(c_2433,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0_38,X1_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),X1_38) ),
    inference(superposition,[status(thm)],[c_1860,c_449])).

cnf(c_16450,plain,
    ( k4_xboole_0(k9_subset_1(sK0,sK0,sK2),X0_38) = k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) ),
    inference(superposition,[status(thm)],[c_13222,c_2433])).

cnf(c_17284,plain,
    ( k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK2,X0_38) ),
    inference(light_normalisation,[status(thm)],[c_16450,c_2445])).

cnf(c_17291,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(demodulation,[status(thm)],[c_16446,c_17284])).

cnf(c_3310,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)),k4_xboole_0(sK2,sK0)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) ),
    inference(superposition,[status(thm)],[c_980,c_602])).

cnf(c_3518,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK2,sK0)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3310,c_1860,c_2436])).

cnf(c_4339,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k9_subset_1(sK0,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_2445,c_3518])).

cnf(c_4388,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4339,c_2445])).

cnf(c_6213,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0_38,k4_xboole_0(sK2,sK0)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) ),
    inference(superposition,[status(thm)],[c_980,c_1218])).

cnf(c_6498,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0_38,k4_xboole_0(sK2,sK0)))) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_6213,c_1860])).

cnf(c_7810,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK2)))) = k9_subset_1(sK0,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_6498,c_1218])).

cnf(c_4745,plain,
    ( k4_xboole_0(k9_subset_1(sK0,sK0,sK2),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_980,c_2433])).

cnf(c_4823,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4745,c_2445])).

cnf(c_4824,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_4823,c_2436])).

cnf(c_8043,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK2))) = k9_subset_1(sK0,sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7810,c_4824])).

cnf(c_17292,plain,
    ( k9_subset_1(sK0,sK2,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_17291,c_4388,c_8043])).

cnf(c_16438,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)),sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) ),
    inference(superposition,[status(thm)],[c_13222,c_2436])).

cnf(c_17303,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)),sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) ),
    inference(demodulation,[status(thm)],[c_16438,c_17284])).

cnf(c_16463,plain,
    ( k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK2,X0_38) ),
    inference(light_normalisation,[status(thm)],[c_16450,c_2445])).

cnf(c_16470,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(demodulation,[status(thm)],[c_16446,c_16463])).

cnf(c_16471,plain,
    ( k9_subset_1(sK0,sK2,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_16470,c_4388,c_8043])).

cnf(c_16449,plain,
    ( k4_xboole_0(k9_subset_1(sK0,sK2,sK2),k4_xboole_0(sK0,X0_38)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) ),
    inference(superposition,[status(thm)],[c_13222,c_2433])).

cnf(c_16464,plain,
    ( k4_xboole_0(k9_subset_1(sK0,sK2,sK2),k4_xboole_0(sK0,X0_38)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) ),
    inference(demodulation,[status(thm)],[c_16449,c_16463])).

cnf(c_16465,plain,
    ( k4_xboole_0(k9_subset_1(sK0,sK2,sK2),k4_xboole_0(sK0,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_16464,c_2436])).

cnf(c_16472,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(demodulation,[status(thm)],[c_16471,c_16465])).

cnf(c_17304,plain,
    ( k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_17303,c_2436,c_16472])).

cnf(c_15529,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,sK0,sK2)))),k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))),sK2) ),
    inference(superposition,[status(thm)],[c_2416,c_11612])).

cnf(c_11659,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)),k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)),sK2) ),
    inference(superposition,[status(thm)],[c_9751,c_11612])).

cnf(c_2443,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK2,X1_38))) = k9_subset_1(sK0,k4_xboole_0(X0_38,X1_38),sK2) ),
    inference(superposition,[status(thm)],[c_1860,c_667])).

cnf(c_2450,plain,
    ( k9_subset_1(sK0,k4_xboole_0(X0_38,X1_38),sK2) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),X1_38) ),
    inference(demodulation,[status(thm)],[c_2425,c_2443])).

cnf(c_11812,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) ),
    inference(demodulation,[status(thm)],[c_11659,c_2445,c_2450])).

cnf(c_15773,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))),sK2) = k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_15529,c_1860,c_2445,c_11812])).

cnf(c_18059,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))),sK2) = k4_xboole_0(sK2,X0_38) ),
    inference(light_normalisation,[status(thm)],[c_15773,c_15773,c_17284])).

cnf(c_388,plain,
    ( k5_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)))) = k4_xboole_0(k4_xboole_0(X0_38,X1_38),X0_38) ),
    inference(superposition,[status(thm)],[c_107,c_381])).

cnf(c_2432,plain,
    ( k5_xboole_0(k4_xboole_0(sK2,X0_38),k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(k4_xboole_0(sK2,X0_38),sK2) ),
    inference(superposition,[status(thm)],[c_1860,c_388])).

cnf(c_18080,plain,
    ( k5_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))),k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))),sK2) ),
    inference(superposition,[status(thm)],[c_18059,c_2432])).

cnf(c_2435,plain,
    ( k5_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK2,X0_38) ),
    inference(superposition,[status(thm)],[c_1860,c_381])).

cnf(c_18084,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k5_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) ),
    inference(superposition,[status(thm)],[c_18059,c_2435])).

cnf(c_11689,plain,
    ( k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),sK2),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) ),
    inference(superposition,[status(thm)],[c_11612,c_2433])).

cnf(c_4733,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))))) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),sK2),X2_38) ),
    inference(superposition,[status(thm)],[c_611,c_2433])).

cnf(c_4831,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),sK2),X2_38) ),
    inference(demodulation,[status(thm)],[c_4733,c_2433])).

cnf(c_4832,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,X1_38)),X2_38) ),
    inference(demodulation,[status(thm)],[c_4831,c_2450])).

cnf(c_11755,plain,
    ( k4_xboole_0(k9_subset_1(sK0,sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2) ),
    inference(demodulation,[status(thm)],[c_11689,c_2436,c_2450,c_4832])).

cnf(c_11756,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_11755,c_2445])).

cnf(c_16400,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)) ),
    inference(superposition,[status(thm)],[c_13222,c_108])).

cnf(c_17351,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) = k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)) ),
    inference(demodulation,[status(thm)],[c_16400,c_17284])).

cnf(c_17352,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_17351,c_16472])).

cnf(c_18088,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_18084,c_11756,c_17352])).

cnf(c_18092,plain,
    ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK2) ),
    inference(demodulation,[status(thm)],[c_18080,c_18088])).

cnf(c_10071,plain,
    ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_9751,c_381])).

cnf(c_18093,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_18092,c_2436,c_10071])).

cnf(c_19113,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0) ),
    inference(light_normalisation,[status(thm)],[c_18893,c_1860,c_2436,c_17292,c_17304,c_18093])).

cnf(c_621,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)),X2_38)) = k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38)) ),
    inference(superposition,[status(thm)],[c_449,c_108])).

cnf(c_674,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38)) ),
    inference(demodulation,[status(thm)],[c_621,c_105])).

cnf(c_2411,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK2)))) = k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK2))) ),
    inference(superposition,[status(thm)],[c_1860,c_674])).

cnf(c_19889,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0))) = k4_xboole_0(X0_38,k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,sK2))) ),
    inference(superposition,[status(thm)],[c_19113,c_2411])).

cnf(c_2427,plain,
    ( k5_xboole_0(X0_38,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(X0_38,sK2) ),
    inference(superposition,[status(thm)],[c_1860,c_108])).

cnf(c_4747,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) ),
    inference(superposition,[status(thm)],[c_1860,c_2433])).

cnf(c_4820,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,sK2)) = k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2) ),
    inference(demodulation,[status(thm)],[c_4747,c_2436])).

cnf(c_383,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_107,c_108])).

cnf(c_10070,plain,
    ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0)) ),
    inference(superposition,[status(thm)],[c_9751,c_383])).

cnf(c_4363,plain,
    ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_3518,c_108])).

cnf(c_4370,plain,
    ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2))) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(demodulation,[status(thm)],[c_4363,c_3518])).

cnf(c_10079,plain,
    ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_10070,c_4370])).

cnf(c_19895,plain,
    ( k4_xboole_0(X0_38,k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2)) = k4_xboole_0(X0_38,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19889,c_2427,c_4820,c_10079])).

cnf(c_19896,plain,
    ( k4_xboole_0(X0_38,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(X0_38,sK2) ),
    inference(demodulation,[status(thm)],[c_19895,c_17304])).

cnf(c_20163,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X0_38,sK2),X1_38))) = k4_xboole_0(k4_xboole_0(X0_38,sK2),X1_38) ),
    inference(light_normalisation,[status(thm)],[c_2422,c_2422,c_19896])).

cnf(c_50570,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k9_subset_1(sK0,X0_38,sK1))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X0_38)))) ),
    inference(superposition,[status(thm)],[c_23296,c_20163])).

cnf(c_6840,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,X0_38),X1_38)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38) ),
    inference(superposition,[status(thm)],[c_2571,c_107])).

cnf(c_23411,plain,
    ( k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK1),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0_38)) ),
    inference(superposition,[status(thm)],[c_23310,c_2582])).

cnf(c_23416,plain,
    ( k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK1),sK1) = k9_subset_1(sK0,X0_38,sK1) ),
    inference(light_normalisation,[status(thm)],[c_23411,c_2582])).

cnf(c_13137,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X2_38)))) = k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(sK1,X2_38),k4_xboole_0(sK1,X1_38))) ),
    inference(superposition,[status(thm)],[c_2582,c_3817])).

cnf(c_13181,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(sK1,X1_38),k4_xboole_0(sK1,X2_38))) = k4_xboole_0(X0_38,k4_xboole_0(k9_subset_1(sK0,X2_38,sK1),X1_38)) ),
    inference(demodulation,[status(thm)],[c_13137,c_108])).

cnf(c_25070,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,X1_38),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) ),
    inference(superposition,[status(thm)],[c_13181,c_17091])).

cnf(c_25084,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38)) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(sK1,X0_38),sK1),X1_38) ),
    inference(superposition,[status(thm)],[c_13181,c_2571])).

cnf(c_3134,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK1,X0_38),sK1) = k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK1)) ),
    inference(superposition,[status(thm)],[c_2582,c_2582])).

cnf(c_21597,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(sK1,X1_38))) = k4_xboole_0(k4_xboole_0(sK1,X1_38),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) ),
    inference(superposition,[status(thm)],[c_2582,c_17091])).

cnf(c_6837,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38),X2_38) ),
    inference(superposition,[status(thm)],[c_2571,c_449])).

cnf(c_6876,plain,
    ( k9_subset_1(sK0,k4_xboole_0(sK1,X0_38),sK1) = k4_xboole_0(k9_subset_1(sK0,sK1,sK1),X0_38) ),
    inference(superposition,[status(thm)],[c_2571,c_2582])).

cnf(c_6893,plain,
    ( k4_xboole_0(k9_subset_1(sK0,sK1,sK1),X0_38) = k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_6876,c_3134])).

cnf(c_22294,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,k9_subset_1(sK0,X1_38,sK1)),X0_38) ),
    inference(demodulation,[status(thm)],[c_21597,c_6837,c_6893])).

cnf(c_25123,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK1)),X1_38) ),
    inference(light_normalisation,[status(thm)],[c_25084,c_3134,c_22294])).

cnf(c_25124,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,X0_38),X1_38) ),
    inference(demodulation,[status(thm)],[c_25123,c_22294,c_23310])).

cnf(c_25142,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,X1_38),X0_38) ),
    inference(demodulation,[status(thm)],[c_25070,c_25124])).

cnf(c_17171,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,X1_38),X0_38)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38) ),
    inference(superposition,[status(thm)],[c_13154,c_6840])).

cnf(c_21522,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,X2_38))) = k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38)))) ),
    inference(superposition,[status(thm)],[c_611,c_17091])).

cnf(c_620,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)),X2_38),X3_38) ),
    inference(superposition,[status(thm)],[c_449,c_105])).

cnf(c_675,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X3_38))) ),
    inference(demodulation,[status(thm)],[c_620,c_105])).

cnf(c_5464,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,X1_38),X1_38),X2_38))) = k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,X1_38)))) ),
    inference(superposition,[status(thm)],[c_667,c_675])).

cnf(c_5640,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X2_38,X3_38))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X2_38,X1_38),X3_38))) ),
    inference(superposition,[status(thm)],[c_675,c_642])).

cnf(c_22358,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,X1_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38))) ),
    inference(demodulation,[status(thm)],[c_21522,c_5464,c_5640])).

cnf(c_25143,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X0_38),X1_38))) = k4_xboole_0(k4_xboole_0(sK1,X0_38),X1_38) ),
    inference(demodulation,[status(thm)],[c_25142,c_611,c_17171,c_22358])).

cnf(c_50586,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X0_38)) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_50570,c_6840,c_23416,c_25143])).

cnf(c_1370,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2))) = k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_980,c_674])).

cnf(c_619,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)),X2_38))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) ),
    inference(superposition,[status(thm)],[c_449,c_108])).

cnf(c_676,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38))))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) ),
    inference(demodulation,[status(thm)],[c_619,c_105])).

cnf(c_10073,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)))) ),
    inference(superposition,[status(thm)],[c_9751,c_676])).

cnf(c_10078,plain,
    ( k5_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)) ),
    inference(demodulation,[status(thm)],[c_10073,c_9751])).

cnf(c_58676,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1370,c_1370,c_1860,c_10078])).

cnf(c_58740,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k9_subset_1(sK0,sK0,sK2)),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) ),
    inference(superposition,[status(thm)],[c_58676,c_3238])).

cnf(c_1863,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) = k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_974,c_261])).

cnf(c_11621,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X0_38,sK2) ),
    inference(superposition,[status(thm)],[c_107,c_11612])).

cnf(c_11964,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),sK2)) ),
    inference(superposition,[status(thm)],[c_11621,c_674])).

cnf(c_11965,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),sK2))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k9_subset_1(sK0,X0_38,sK2)) ),
    inference(superposition,[status(thm)],[c_11621,c_642])).

cnf(c_11988,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k9_subset_1(sK0,X0_38,sK2)) ),
    inference(demodulation,[status(thm)],[c_11965,c_611])).

cnf(c_9234,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) ),
    inference(superposition,[status(thm)],[c_980,c_3238])).

cnf(c_9735,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) ),
    inference(light_normalisation,[status(thm)],[c_9234,c_1863])).

cnf(c_9736,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) ),
    inference(demodulation,[status(thm)],[c_9735,c_667])).

cnf(c_11989,plain,
    ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_11988,c_1863,c_9736])).

cnf(c_11990,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),sK2)) = k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2)))) ),
    inference(demodulation,[status(thm)],[c_11964,c_11989])).

cnf(c_11991,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2)) ),
    inference(demodulation,[status(thm)],[c_11990,c_108,c_611])).

cnf(c_11992,plain,
    ( k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_11991,c_1863])).

cnf(c_1077,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38))) = k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38) ),
    inference(superposition,[status(thm)],[c_980,c_611])).

cnf(c_1367,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38))))) = k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38))) ),
    inference(superposition,[status(thm)],[c_107,c_674])).

cnf(c_16174,plain,
    ( k5_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38))) = k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) ),
    inference(superposition,[status(thm)],[c_1077,c_1367])).

cnf(c_16190,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_16174,c_381])).

cnf(c_16175,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) ),
    inference(superposition,[status(thm)],[c_1077,c_1218])).

cnf(c_16189,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) ),
    inference(demodulation,[status(thm)],[c_16175,c_667])).

cnf(c_16191,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) ),
    inference(demodulation,[status(thm)],[c_16190,c_16189])).

cnf(c_16192,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) = k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_16191,c_1863])).

cnf(c_58823,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) = k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_58740,c_1863,c_2445,c_11992,c_16192])).

cnf(c_108773,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_108772,c_2591,c_50586,c_58823])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_101,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
    | k7_subset_1(X1_38,X0_38,X2_38) = k4_xboole_0(X0_38,X2_38) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_260,plain,
    ( k7_subset_1(X0_38,X1_38,X2_38) = k4_xboole_0(X1_38,X2_38)
    | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_1094,plain,
    ( k7_subset_1(sK0,sK1,X0_38) = k4_xboole_0(sK1,X0_38) ),
    inference(superposition,[status(thm)],[c_263,c_260])).

cnf(c_9,negated_conjecture,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_99,negated_conjecture,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_783,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k7_subset_1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_476,c_99])).

cnf(c_1493,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1094,c_783])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_108773,c_1493])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:39:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.11/7.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.11/7.50  
% 55.11/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.11/7.50  
% 55.11/7.50  ------  iProver source info
% 55.11/7.50  
% 55.11/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.11/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.11/7.50  git: non_committed_changes: false
% 55.11/7.50  git: last_make_outside_of_git: false
% 55.11/7.50  
% 55.11/7.50  ------ 
% 55.11/7.50  
% 55.11/7.50  ------ Input Options
% 55.11/7.50  
% 55.11/7.50  --out_options                           all
% 55.11/7.50  --tptp_safe_out                         true
% 55.11/7.50  --problem_path                          ""
% 55.11/7.50  --include_path                          ""
% 55.11/7.50  --clausifier                            res/vclausify_rel
% 55.11/7.50  --clausifier_options                    ""
% 55.11/7.50  --stdin                                 false
% 55.11/7.50  --stats_out                             all
% 55.11/7.50  
% 55.11/7.50  ------ General Options
% 55.11/7.50  
% 55.11/7.50  --fof                                   false
% 55.11/7.50  --time_out_real                         305.
% 55.11/7.50  --time_out_virtual                      -1.
% 55.11/7.50  --symbol_type_check                     false
% 55.11/7.50  --clausify_out                          false
% 55.11/7.50  --sig_cnt_out                           false
% 55.11/7.50  --trig_cnt_out                          false
% 55.11/7.50  --trig_cnt_out_tolerance                1.
% 55.11/7.50  --trig_cnt_out_sk_spl                   false
% 55.11/7.50  --abstr_cl_out                          false
% 55.11/7.50  
% 55.11/7.50  ------ Global Options
% 55.11/7.50  
% 55.11/7.50  --schedule                              default
% 55.11/7.50  --add_important_lit                     false
% 55.11/7.50  --prop_solver_per_cl                    1000
% 55.11/7.50  --min_unsat_core                        false
% 55.11/7.50  --soft_assumptions                      false
% 55.11/7.50  --soft_lemma_size                       3
% 55.11/7.50  --prop_impl_unit_size                   0
% 55.11/7.50  --prop_impl_unit                        []
% 55.11/7.50  --share_sel_clauses                     true
% 55.11/7.50  --reset_solvers                         false
% 55.11/7.50  --bc_imp_inh                            [conj_cone]
% 55.11/7.50  --conj_cone_tolerance                   3.
% 55.11/7.50  --extra_neg_conj                        none
% 55.11/7.50  --large_theory_mode                     true
% 55.11/7.50  --prolific_symb_bound                   200
% 55.11/7.50  --lt_threshold                          2000
% 55.11/7.50  --clause_weak_htbl                      true
% 55.11/7.50  --gc_record_bc_elim                     false
% 55.11/7.50  
% 55.11/7.50  ------ Preprocessing Options
% 55.11/7.50  
% 55.11/7.50  --preprocessing_flag                    true
% 55.11/7.50  --time_out_prep_mult                    0.1
% 55.11/7.50  --splitting_mode                        input
% 55.11/7.50  --splitting_grd                         true
% 55.11/7.50  --splitting_cvd                         false
% 55.11/7.50  --splitting_cvd_svl                     false
% 55.11/7.50  --splitting_nvd                         32
% 55.11/7.50  --sub_typing                            true
% 55.11/7.50  --prep_gs_sim                           true
% 55.11/7.50  --prep_unflatten                        true
% 55.11/7.50  --prep_res_sim                          true
% 55.11/7.50  --prep_upred                            true
% 55.11/7.50  --prep_sem_filter                       exhaustive
% 55.11/7.50  --prep_sem_filter_out                   false
% 55.11/7.50  --pred_elim                             true
% 55.11/7.50  --res_sim_input                         true
% 55.11/7.50  --eq_ax_congr_red                       true
% 55.11/7.50  --pure_diseq_elim                       true
% 55.11/7.50  --brand_transform                       false
% 55.11/7.50  --non_eq_to_eq                          false
% 55.11/7.50  --prep_def_merge                        true
% 55.11/7.50  --prep_def_merge_prop_impl              false
% 55.11/7.50  --prep_def_merge_mbd                    true
% 55.11/7.50  --prep_def_merge_tr_red                 false
% 55.11/7.50  --prep_def_merge_tr_cl                  false
% 55.11/7.50  --smt_preprocessing                     true
% 55.11/7.50  --smt_ac_axioms                         fast
% 55.11/7.50  --preprocessed_out                      false
% 55.11/7.50  --preprocessed_stats                    false
% 55.11/7.50  
% 55.11/7.50  ------ Abstraction refinement Options
% 55.11/7.50  
% 55.11/7.50  --abstr_ref                             []
% 55.11/7.50  --abstr_ref_prep                        false
% 55.11/7.50  --abstr_ref_until_sat                   false
% 55.11/7.50  --abstr_ref_sig_restrict                funpre
% 55.11/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.11/7.50  --abstr_ref_under                       []
% 55.11/7.50  
% 55.11/7.50  ------ SAT Options
% 55.11/7.50  
% 55.11/7.50  --sat_mode                              false
% 55.11/7.50  --sat_fm_restart_options                ""
% 55.11/7.50  --sat_gr_def                            false
% 55.11/7.50  --sat_epr_types                         true
% 55.11/7.50  --sat_non_cyclic_types                  false
% 55.11/7.50  --sat_finite_models                     false
% 55.11/7.50  --sat_fm_lemmas                         false
% 55.11/7.50  --sat_fm_prep                           false
% 55.11/7.50  --sat_fm_uc_incr                        true
% 55.11/7.50  --sat_out_model                         small
% 55.11/7.50  --sat_out_clauses                       false
% 55.11/7.50  
% 55.11/7.50  ------ QBF Options
% 55.11/7.50  
% 55.11/7.50  --qbf_mode                              false
% 55.11/7.50  --qbf_elim_univ                         false
% 55.11/7.50  --qbf_dom_inst                          none
% 55.11/7.50  --qbf_dom_pre_inst                      false
% 55.11/7.50  --qbf_sk_in                             false
% 55.11/7.50  --qbf_pred_elim                         true
% 55.11/7.50  --qbf_split                             512
% 55.11/7.50  
% 55.11/7.50  ------ BMC1 Options
% 55.11/7.50  
% 55.11/7.50  --bmc1_incremental                      false
% 55.11/7.50  --bmc1_axioms                           reachable_all
% 55.11/7.50  --bmc1_min_bound                        0
% 55.11/7.50  --bmc1_max_bound                        -1
% 55.11/7.50  --bmc1_max_bound_default                -1
% 55.11/7.50  --bmc1_symbol_reachability              true
% 55.11/7.50  --bmc1_property_lemmas                  false
% 55.11/7.50  --bmc1_k_induction                      false
% 55.11/7.50  --bmc1_non_equiv_states                 false
% 55.11/7.50  --bmc1_deadlock                         false
% 55.11/7.50  --bmc1_ucm                              false
% 55.11/7.50  --bmc1_add_unsat_core                   none
% 55.11/7.50  --bmc1_unsat_core_children              false
% 55.11/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.11/7.50  --bmc1_out_stat                         full
% 55.11/7.50  --bmc1_ground_init                      false
% 55.11/7.50  --bmc1_pre_inst_next_state              false
% 55.11/7.50  --bmc1_pre_inst_state                   false
% 55.11/7.50  --bmc1_pre_inst_reach_state             false
% 55.11/7.50  --bmc1_out_unsat_core                   false
% 55.11/7.50  --bmc1_aig_witness_out                  false
% 55.11/7.50  --bmc1_verbose                          false
% 55.11/7.50  --bmc1_dump_clauses_tptp                false
% 55.11/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.11/7.50  --bmc1_dump_file                        -
% 55.11/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.11/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.11/7.50  --bmc1_ucm_extend_mode                  1
% 55.11/7.50  --bmc1_ucm_init_mode                    2
% 55.11/7.50  --bmc1_ucm_cone_mode                    none
% 55.11/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.11/7.50  --bmc1_ucm_relax_model                  4
% 55.11/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.11/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.11/7.50  --bmc1_ucm_layered_model                none
% 55.11/7.50  --bmc1_ucm_max_lemma_size               10
% 55.11/7.50  
% 55.11/7.50  ------ AIG Options
% 55.11/7.50  
% 55.11/7.50  --aig_mode                              false
% 55.11/7.50  
% 55.11/7.50  ------ Instantiation Options
% 55.11/7.50  
% 55.11/7.50  --instantiation_flag                    true
% 55.11/7.50  --inst_sos_flag                         true
% 55.11/7.50  --inst_sos_phase                        true
% 55.11/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.11/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.11/7.50  --inst_lit_sel_side                     num_symb
% 55.11/7.50  --inst_solver_per_active                1400
% 55.11/7.50  --inst_solver_calls_frac                1.
% 55.11/7.50  --inst_passive_queue_type               priority_queues
% 55.11/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.11/7.50  --inst_passive_queues_freq              [25;2]
% 55.11/7.50  --inst_dismatching                      true
% 55.11/7.50  --inst_eager_unprocessed_to_passive     true
% 55.11/7.50  --inst_prop_sim_given                   true
% 55.11/7.50  --inst_prop_sim_new                     false
% 55.11/7.50  --inst_subs_new                         false
% 55.11/7.50  --inst_eq_res_simp                      false
% 55.11/7.50  --inst_subs_given                       false
% 55.11/7.50  --inst_orphan_elimination               true
% 55.11/7.50  --inst_learning_loop_flag               true
% 55.11/7.50  --inst_learning_start                   3000
% 55.11/7.50  --inst_learning_factor                  2
% 55.11/7.50  --inst_start_prop_sim_after_learn       3
% 55.11/7.50  --inst_sel_renew                        solver
% 55.11/7.50  --inst_lit_activity_flag                true
% 55.11/7.50  --inst_restr_to_given                   false
% 55.11/7.50  --inst_activity_threshold               500
% 55.11/7.50  --inst_out_proof                        true
% 55.11/7.50  
% 55.11/7.50  ------ Resolution Options
% 55.11/7.50  
% 55.11/7.50  --resolution_flag                       true
% 55.11/7.50  --res_lit_sel                           adaptive
% 55.11/7.50  --res_lit_sel_side                      none
% 55.11/7.50  --res_ordering                          kbo
% 55.11/7.50  --res_to_prop_solver                    active
% 55.11/7.50  --res_prop_simpl_new                    false
% 55.11/7.50  --res_prop_simpl_given                  true
% 55.11/7.50  --res_passive_queue_type                priority_queues
% 55.11/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.11/7.50  --res_passive_queues_freq               [15;5]
% 55.11/7.50  --res_forward_subs                      full
% 55.11/7.50  --res_backward_subs                     full
% 55.11/7.50  --res_forward_subs_resolution           true
% 55.11/7.50  --res_backward_subs_resolution          true
% 55.11/7.50  --res_orphan_elimination                true
% 55.11/7.50  --res_time_limit                        2.
% 55.11/7.50  --res_out_proof                         true
% 55.11/7.50  
% 55.11/7.50  ------ Superposition Options
% 55.11/7.50  
% 55.11/7.50  --superposition_flag                    true
% 55.11/7.50  --sup_passive_queue_type                priority_queues
% 55.11/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.11/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.11/7.50  --demod_completeness_check              fast
% 55.11/7.50  --demod_use_ground                      true
% 55.11/7.50  --sup_to_prop_solver                    passive
% 55.11/7.50  --sup_prop_simpl_new                    true
% 55.11/7.50  --sup_prop_simpl_given                  true
% 55.11/7.50  --sup_fun_splitting                     true
% 55.11/7.50  --sup_smt_interval                      50000
% 55.11/7.50  
% 55.11/7.50  ------ Superposition Simplification Setup
% 55.11/7.50  
% 55.11/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.11/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.11/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.11/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.11/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.11/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.11/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.11/7.50  --sup_immed_triv                        [TrivRules]
% 55.11/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.11/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.11/7.50  --sup_immed_bw_main                     []
% 55.11/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.11/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.11/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.11/7.50  --sup_input_bw                          []
% 55.11/7.50  
% 55.11/7.50  ------ Combination Options
% 55.11/7.50  
% 55.11/7.50  --comb_res_mult                         3
% 55.11/7.50  --comb_sup_mult                         2
% 55.11/7.50  --comb_inst_mult                        10
% 55.11/7.50  
% 55.11/7.50  ------ Debug Options
% 55.11/7.50  
% 55.11/7.50  --dbg_backtrace                         false
% 55.11/7.50  --dbg_dump_prop_clauses                 false
% 55.11/7.50  --dbg_dump_prop_clauses_file            -
% 55.11/7.50  --dbg_out_stat                          false
% 55.11/7.50  ------ Parsing...
% 55.11/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.11/7.50  
% 55.11/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.11/7.50  
% 55.11/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.11/7.50  
% 55.11/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.11/7.50  ------ Proving...
% 55.11/7.50  ------ Problem Properties 
% 55.11/7.50  
% 55.11/7.50  
% 55.11/7.50  clauses                                 12
% 55.11/7.50  conjectures                             3
% 55.11/7.50  EPR                                     0
% 55.11/7.50  Horn                                    12
% 55.11/7.50  unary                                   7
% 55.11/7.50  binary                                  5
% 55.11/7.50  lits                                    17
% 55.11/7.50  lits eq                                 9
% 55.11/7.50  fd_pure                                 0
% 55.11/7.50  fd_pseudo                               0
% 55.11/7.50  fd_cond                                 0
% 55.11/7.50  fd_pseudo_cond                          0
% 55.11/7.50  AC symbols                              0
% 55.11/7.50  
% 55.11/7.50  ------ Schedule dynamic 5 is on 
% 55.11/7.50  
% 55.11/7.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.11/7.50  
% 55.11/7.50  
% 55.11/7.50  ------ 
% 55.11/7.50  Current options:
% 55.11/7.50  ------ 
% 55.11/7.50  
% 55.11/7.50  ------ Input Options
% 55.11/7.50  
% 55.11/7.50  --out_options                           all
% 55.11/7.50  --tptp_safe_out                         true
% 55.11/7.50  --problem_path                          ""
% 55.11/7.50  --include_path                          ""
% 55.11/7.50  --clausifier                            res/vclausify_rel
% 55.11/7.50  --clausifier_options                    ""
% 55.11/7.50  --stdin                                 false
% 55.11/7.50  --stats_out                             all
% 55.11/7.50  
% 55.11/7.50  ------ General Options
% 55.11/7.50  
% 55.11/7.50  --fof                                   false
% 55.11/7.50  --time_out_real                         305.
% 55.11/7.50  --time_out_virtual                      -1.
% 55.11/7.50  --symbol_type_check                     false
% 55.11/7.50  --clausify_out                          false
% 55.11/7.50  --sig_cnt_out                           false
% 55.11/7.50  --trig_cnt_out                          false
% 55.11/7.50  --trig_cnt_out_tolerance                1.
% 55.11/7.50  --trig_cnt_out_sk_spl                   false
% 55.11/7.50  --abstr_cl_out                          false
% 55.11/7.50  
% 55.11/7.50  ------ Global Options
% 55.11/7.50  
% 55.11/7.50  --schedule                              default
% 55.11/7.50  --add_important_lit                     false
% 55.11/7.50  --prop_solver_per_cl                    1000
% 55.11/7.50  --min_unsat_core                        false
% 55.11/7.50  --soft_assumptions                      false
% 55.11/7.50  --soft_lemma_size                       3
% 55.11/7.50  --prop_impl_unit_size                   0
% 55.11/7.50  --prop_impl_unit                        []
% 55.11/7.50  --share_sel_clauses                     true
% 55.11/7.50  --reset_solvers                         false
% 55.11/7.50  --bc_imp_inh                            [conj_cone]
% 55.11/7.50  --conj_cone_tolerance                   3.
% 55.11/7.50  --extra_neg_conj                        none
% 55.11/7.50  --large_theory_mode                     true
% 55.11/7.50  --prolific_symb_bound                   200
% 55.11/7.50  --lt_threshold                          2000
% 55.11/7.50  --clause_weak_htbl                      true
% 55.11/7.50  --gc_record_bc_elim                     false
% 55.11/7.50  
% 55.11/7.50  ------ Preprocessing Options
% 55.11/7.50  
% 55.11/7.50  --preprocessing_flag                    true
% 55.11/7.50  --time_out_prep_mult                    0.1
% 55.11/7.50  --splitting_mode                        input
% 55.11/7.50  --splitting_grd                         true
% 55.11/7.50  --splitting_cvd                         false
% 55.11/7.50  --splitting_cvd_svl                     false
% 55.11/7.50  --splitting_nvd                         32
% 55.11/7.50  --sub_typing                            true
% 55.11/7.50  --prep_gs_sim                           true
% 55.11/7.50  --prep_unflatten                        true
% 55.11/7.50  --prep_res_sim                          true
% 55.11/7.50  --prep_upred                            true
% 55.11/7.50  --prep_sem_filter                       exhaustive
% 55.11/7.50  --prep_sem_filter_out                   false
% 55.11/7.50  --pred_elim                             true
% 55.11/7.50  --res_sim_input                         true
% 55.11/7.50  --eq_ax_congr_red                       true
% 55.11/7.50  --pure_diseq_elim                       true
% 55.11/7.50  --brand_transform                       false
% 55.11/7.50  --non_eq_to_eq                          false
% 55.11/7.50  --prep_def_merge                        true
% 55.11/7.50  --prep_def_merge_prop_impl              false
% 55.11/7.50  --prep_def_merge_mbd                    true
% 55.11/7.50  --prep_def_merge_tr_red                 false
% 55.11/7.50  --prep_def_merge_tr_cl                  false
% 55.11/7.50  --smt_preprocessing                     true
% 55.11/7.50  --smt_ac_axioms                         fast
% 55.11/7.50  --preprocessed_out                      false
% 55.11/7.50  --preprocessed_stats                    false
% 55.11/7.50  
% 55.11/7.50  ------ Abstraction refinement Options
% 55.11/7.50  
% 55.11/7.50  --abstr_ref                             []
% 55.11/7.50  --abstr_ref_prep                        false
% 55.11/7.50  --abstr_ref_until_sat                   false
% 55.11/7.50  --abstr_ref_sig_restrict                funpre
% 55.11/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.11/7.50  --abstr_ref_under                       []
% 55.11/7.50  
% 55.11/7.50  ------ SAT Options
% 55.11/7.50  
% 55.11/7.50  --sat_mode                              false
% 55.11/7.50  --sat_fm_restart_options                ""
% 55.11/7.50  --sat_gr_def                            false
% 55.11/7.50  --sat_epr_types                         true
% 55.11/7.50  --sat_non_cyclic_types                  false
% 55.11/7.50  --sat_finite_models                     false
% 55.11/7.50  --sat_fm_lemmas                         false
% 55.11/7.50  --sat_fm_prep                           false
% 55.11/7.50  --sat_fm_uc_incr                        true
% 55.11/7.50  --sat_out_model                         small
% 55.11/7.50  --sat_out_clauses                       false
% 55.11/7.50  
% 55.11/7.50  ------ QBF Options
% 55.11/7.50  
% 55.11/7.50  --qbf_mode                              false
% 55.11/7.50  --qbf_elim_univ                         false
% 55.11/7.50  --qbf_dom_inst                          none
% 55.11/7.50  --qbf_dom_pre_inst                      false
% 55.11/7.50  --qbf_sk_in                             false
% 55.11/7.50  --qbf_pred_elim                         true
% 55.11/7.50  --qbf_split                             512
% 55.11/7.50  
% 55.11/7.50  ------ BMC1 Options
% 55.11/7.50  
% 55.11/7.50  --bmc1_incremental                      false
% 55.11/7.50  --bmc1_axioms                           reachable_all
% 55.11/7.50  --bmc1_min_bound                        0
% 55.11/7.50  --bmc1_max_bound                        -1
% 55.11/7.50  --bmc1_max_bound_default                -1
% 55.11/7.50  --bmc1_symbol_reachability              true
% 55.11/7.50  --bmc1_property_lemmas                  false
% 55.11/7.50  --bmc1_k_induction                      false
% 55.11/7.50  --bmc1_non_equiv_states                 false
% 55.11/7.50  --bmc1_deadlock                         false
% 55.11/7.50  --bmc1_ucm                              false
% 55.11/7.50  --bmc1_add_unsat_core                   none
% 55.11/7.50  --bmc1_unsat_core_children              false
% 55.11/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.11/7.50  --bmc1_out_stat                         full
% 55.11/7.50  --bmc1_ground_init                      false
% 55.11/7.50  --bmc1_pre_inst_next_state              false
% 55.11/7.50  --bmc1_pre_inst_state                   false
% 55.11/7.50  --bmc1_pre_inst_reach_state             false
% 55.11/7.50  --bmc1_out_unsat_core                   false
% 55.11/7.50  --bmc1_aig_witness_out                  false
% 55.11/7.50  --bmc1_verbose                          false
% 55.11/7.50  --bmc1_dump_clauses_tptp                false
% 55.11/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.11/7.50  --bmc1_dump_file                        -
% 55.11/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.11/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.11/7.50  --bmc1_ucm_extend_mode                  1
% 55.11/7.50  --bmc1_ucm_init_mode                    2
% 55.11/7.50  --bmc1_ucm_cone_mode                    none
% 55.11/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.11/7.50  --bmc1_ucm_relax_model                  4
% 55.11/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.11/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.11/7.50  --bmc1_ucm_layered_model                none
% 55.11/7.50  --bmc1_ucm_max_lemma_size               10
% 55.11/7.50  
% 55.11/7.50  ------ AIG Options
% 55.11/7.50  
% 55.11/7.50  --aig_mode                              false
% 55.11/7.50  
% 55.11/7.50  ------ Instantiation Options
% 55.11/7.50  
% 55.11/7.50  --instantiation_flag                    true
% 55.11/7.50  --inst_sos_flag                         true
% 55.11/7.50  --inst_sos_phase                        true
% 55.11/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.11/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.11/7.50  --inst_lit_sel_side                     none
% 55.11/7.50  --inst_solver_per_active                1400
% 55.11/7.50  --inst_solver_calls_frac                1.
% 55.11/7.50  --inst_passive_queue_type               priority_queues
% 55.11/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.11/7.50  --inst_passive_queues_freq              [25;2]
% 55.11/7.50  --inst_dismatching                      true
% 55.11/7.50  --inst_eager_unprocessed_to_passive     true
% 55.11/7.50  --inst_prop_sim_given                   true
% 55.11/7.50  --inst_prop_sim_new                     false
% 55.11/7.50  --inst_subs_new                         false
% 55.11/7.50  --inst_eq_res_simp                      false
% 55.11/7.50  --inst_subs_given                       false
% 55.11/7.50  --inst_orphan_elimination               true
% 55.11/7.50  --inst_learning_loop_flag               true
% 55.11/7.50  --inst_learning_start                   3000
% 55.11/7.50  --inst_learning_factor                  2
% 55.11/7.50  --inst_start_prop_sim_after_learn       3
% 55.11/7.50  --inst_sel_renew                        solver
% 55.11/7.50  --inst_lit_activity_flag                true
% 55.11/7.50  --inst_restr_to_given                   false
% 55.11/7.50  --inst_activity_threshold               500
% 55.11/7.50  --inst_out_proof                        true
% 55.11/7.50  
% 55.11/7.50  ------ Resolution Options
% 55.11/7.50  
% 55.11/7.50  --resolution_flag                       false
% 55.11/7.50  --res_lit_sel                           adaptive
% 55.11/7.50  --res_lit_sel_side                      none
% 55.11/7.50  --res_ordering                          kbo
% 55.11/7.50  --res_to_prop_solver                    active
% 55.11/7.50  --res_prop_simpl_new                    false
% 55.11/7.50  --res_prop_simpl_given                  true
% 55.11/7.50  --res_passive_queue_type                priority_queues
% 55.11/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.11/7.50  --res_passive_queues_freq               [15;5]
% 55.11/7.50  --res_forward_subs                      full
% 55.11/7.50  --res_backward_subs                     full
% 55.11/7.50  --res_forward_subs_resolution           true
% 55.11/7.50  --res_backward_subs_resolution          true
% 55.11/7.50  --res_orphan_elimination                true
% 55.11/7.50  --res_time_limit                        2.
% 55.11/7.50  --res_out_proof                         true
% 55.11/7.50  
% 55.11/7.50  ------ Superposition Options
% 55.11/7.50  
% 55.11/7.50  --superposition_flag                    true
% 55.11/7.50  --sup_passive_queue_type                priority_queues
% 55.11/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.11/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.11/7.50  --demod_completeness_check              fast
% 55.11/7.50  --demod_use_ground                      true
% 55.11/7.50  --sup_to_prop_solver                    passive
% 55.11/7.50  --sup_prop_simpl_new                    true
% 55.11/7.50  --sup_prop_simpl_given                  true
% 55.11/7.50  --sup_fun_splitting                     true
% 55.11/7.50  --sup_smt_interval                      50000
% 55.11/7.50  
% 55.11/7.50  ------ Superposition Simplification Setup
% 55.11/7.50  
% 55.11/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.11/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.11/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.11/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.11/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.11/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.11/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.11/7.50  --sup_immed_triv                        [TrivRules]
% 55.11/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.11/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.11/7.50  --sup_immed_bw_main                     []
% 55.11/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.11/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.11/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.11/7.50  --sup_input_bw                          []
% 55.11/7.50  
% 55.11/7.50  ------ Combination Options
% 55.11/7.50  
% 55.11/7.50  --comb_res_mult                         3
% 55.11/7.50  --comb_sup_mult                         2
% 55.11/7.50  --comb_inst_mult                        10
% 55.11/7.50  
% 55.11/7.50  ------ Debug Options
% 55.11/7.50  
% 55.11/7.50  --dbg_backtrace                         false
% 55.11/7.50  --dbg_dump_prop_clauses                 false
% 55.11/7.50  --dbg_dump_prop_clauses_file            -
% 55.11/7.50  --dbg_out_stat                          false
% 55.11/7.50  
% 55.11/7.50  
% 55.11/7.50  
% 55.11/7.50  
% 55.11/7.50  ------ Proving...
% 55.11/7.50  
% 55.11/7.50  
% 55.11/7.50  % SZS status Theorem for theBenchmark.p
% 55.11/7.50  
% 55.11/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.11/7.50  
% 55.11/7.50  fof(f11,conjecture,(
% 55.11/7.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f12,negated_conjecture,(
% 55.11/7.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 55.11/7.50    inference(negated_conjecture,[],[f11])).
% 55.11/7.50  
% 55.11/7.50  fof(f18,plain,(
% 55.11/7.50    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.11/7.50    inference(ennf_transformation,[],[f12])).
% 55.11/7.50  
% 55.11/7.50  fof(f20,plain,(
% 55.11/7.50    ( ! [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k7_subset_1(X0,X1,sK2) != k9_subset_1(X0,X1,k3_subset_1(X0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 55.11/7.50    introduced(choice_axiom,[])).
% 55.11/7.50  
% 55.11/7.50  fof(f19,plain,(
% 55.11/7.50    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 55.11/7.50    introduced(choice_axiom,[])).
% 55.11/7.50  
% 55.11/7.50  fof(f21,plain,(
% 55.11/7.50    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 55.11/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20,f19])).
% 55.11/7.50  
% 55.11/7.50  fof(f33,plain,(
% 55.11/7.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 55.11/7.50    inference(cnf_transformation,[],[f21])).
% 55.11/7.50  
% 55.11/7.50  fof(f6,axiom,(
% 55.11/7.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f13,plain,(
% 55.11/7.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.11/7.50    inference(ennf_transformation,[],[f6])).
% 55.11/7.50  
% 55.11/7.50  fof(f27,plain,(
% 55.11/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.11/7.50    inference(cnf_transformation,[],[f13])).
% 55.11/7.50  
% 55.11/7.50  fof(f7,axiom,(
% 55.11/7.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f14,plain,(
% 55.11/7.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.11/7.50    inference(ennf_transformation,[],[f7])).
% 55.11/7.50  
% 55.11/7.50  fof(f28,plain,(
% 55.11/7.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.11/7.50    inference(cnf_transformation,[],[f14])).
% 55.11/7.50  
% 55.11/7.50  fof(f8,axiom,(
% 55.11/7.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f15,plain,(
% 55.11/7.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.11/7.50    inference(ennf_transformation,[],[f8])).
% 55.11/7.50  
% 55.11/7.50  fof(f29,plain,(
% 55.11/7.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.11/7.50    inference(cnf_transformation,[],[f15])).
% 55.11/7.50  
% 55.11/7.50  fof(f32,plain,(
% 55.11/7.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 55.11/7.50    inference(cnf_transformation,[],[f21])).
% 55.11/7.50  
% 55.11/7.50  fof(f1,axiom,(
% 55.11/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f22,plain,(
% 55.11/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 55.11/7.50    inference(cnf_transformation,[],[f1])).
% 55.11/7.50  
% 55.11/7.50  fof(f4,axiom,(
% 55.11/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f25,plain,(
% 55.11/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 55.11/7.50    inference(cnf_transformation,[],[f4])).
% 55.11/7.50  
% 55.11/7.50  fof(f36,plain,(
% 55.11/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 55.11/7.50    inference(definition_unfolding,[],[f22,f25,f25])).
% 55.11/7.50  
% 55.11/7.50  fof(f5,axiom,(
% 55.11/7.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f26,plain,(
% 55.11/7.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 55.11/7.50    inference(cnf_transformation,[],[f5])).
% 55.11/7.50  
% 55.11/7.50  fof(f38,plain,(
% 55.11/7.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 55.11/7.50    inference(definition_unfolding,[],[f26,f25,f25])).
% 55.11/7.50  
% 55.11/7.50  fof(f3,axiom,(
% 55.11/7.50    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f24,plain,(
% 55.11/7.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 55.11/7.50    inference(cnf_transformation,[],[f3])).
% 55.11/7.50  
% 55.11/7.50  fof(f37,plain,(
% 55.11/7.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 55.11/7.50    inference(definition_unfolding,[],[f24,f25,f25,f25,f25])).
% 55.11/7.50  
% 55.11/7.50  fof(f10,axiom,(
% 55.11/7.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f17,plain,(
% 55.11/7.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 55.11/7.50    inference(ennf_transformation,[],[f10])).
% 55.11/7.50  
% 55.11/7.50  fof(f31,plain,(
% 55.11/7.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 55.11/7.50    inference(cnf_transformation,[],[f17])).
% 55.11/7.50  
% 55.11/7.50  fof(f39,plain,(
% 55.11/7.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 55.11/7.50    inference(definition_unfolding,[],[f31,f25])).
% 55.11/7.50  
% 55.11/7.50  fof(f2,axiom,(
% 55.11/7.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f23,plain,(
% 55.11/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.11/7.50    inference(cnf_transformation,[],[f2])).
% 55.11/7.50  
% 55.11/7.50  fof(f35,plain,(
% 55.11/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.11/7.50    inference(definition_unfolding,[],[f23,f25])).
% 55.11/7.50  
% 55.11/7.50  fof(f9,axiom,(
% 55.11/7.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 55.11/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.11/7.50  
% 55.11/7.50  fof(f16,plain,(
% 55.11/7.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.11/7.50    inference(ennf_transformation,[],[f9])).
% 55.11/7.50  
% 55.11/7.50  fof(f30,plain,(
% 55.11/7.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.11/7.50    inference(cnf_transformation,[],[f16])).
% 55.11/7.50  
% 55.11/7.50  fof(f34,plain,(
% 55.11/7.50    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 55.11/7.50    inference(cnf_transformation,[],[f21])).
% 55.11/7.50  
% 55.11/7.50  cnf(c_10,negated_conjecture,
% 55.11/7.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 55.11/7.50      inference(cnf_transformation,[],[f33]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_98,negated_conjecture,
% 55.11/7.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_10]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_262,plain,
% 55.11/7.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 55.11/7.50      inference(predicate_to_equality,[status(thm)],[c_98]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4,plain,
% 55.11/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.11/7.50      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 55.11/7.50      inference(cnf_transformation,[],[f27]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_104,plain,
% 55.11/7.50      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 55.11/7.50      | k3_subset_1(X1_38,X0_38) = k4_xboole_0(X1_38,X0_38) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_4]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_257,plain,
% 55.11/7.50      ( k3_subset_1(X0_38,X1_38) = k4_xboole_0(X0_38,X1_38)
% 55.11/7.50      | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
% 55.11/7.50      inference(predicate_to_equality,[status(thm)],[c_104]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_476,plain,
% 55.11/7.50      ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_262,c_257]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_5,plain,
% 55.11/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.11/7.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 55.11/7.50      inference(cnf_transformation,[],[f28]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_103,plain,
% 55.11/7.50      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 55.11/7.50      | m1_subset_1(k3_subset_1(X1_38,X0_38),k1_zfmisc_1(X1_38)) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_5]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_258,plain,
% 55.11/7.50      ( m1_subset_1(X0_38,k1_zfmisc_1(X1_38)) != iProver_top
% 55.11/7.50      | m1_subset_1(k3_subset_1(X1_38,X0_38),k1_zfmisc_1(X1_38)) = iProver_top ),
% 55.11/7.50      inference(predicate_to_equality,[status(thm)],[c_103]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_784,plain,
% 55.11/7.50      ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
% 55.11/7.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_476,c_258]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_13,plain,
% 55.11/7.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 55.11/7.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_974,plain,
% 55.11/7.50      ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 55.11/7.50      inference(global_propositional_subsumption,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_784,c_13]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_979,plain,
% 55.11/7.50      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_974,c_257]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6,plain,
% 55.11/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.11/7.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 55.11/7.50      inference(cnf_transformation,[],[f29]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_102,plain,
% 55.11/7.50      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 55.11/7.50      | k3_subset_1(X1_38,k3_subset_1(X1_38,X0_38)) = X0_38 ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_6]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_259,plain,
% 55.11/7.50      ( k3_subset_1(X0_38,k3_subset_1(X0_38,X1_38)) = X1_38
% 55.11/7.50      | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
% 55.11/7.50      inference(predicate_to_equality,[status(thm)],[c_102]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_526,plain,
% 55.11/7.50      ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_262,c_259]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_530,plain,
% 55.11/7.50      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_526,c_476]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_980,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = sK2 ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_979,c_530]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11,negated_conjecture,
% 55.11/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 55.11/7.50      inference(cnf_transformation,[],[f32]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_97,negated_conjecture,
% 55.11/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_11]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_263,plain,
% 55.11/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 55.11/7.50      inference(predicate_to_equality,[status(thm)],[c_97]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_477,plain,
% 55.11/7.50      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_263,c_257]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_855,plain,
% 55.11/7.50      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 55.11/7.50      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_477,c_258]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_12,plain,
% 55.11/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 55.11/7.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_983,plain,
% 55.11/7.50      ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 55.11/7.50      inference(global_propositional_subsumption,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_855,c_12]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_988,plain,
% 55.11/7.50      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_983,c_257]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_527,plain,
% 55.11/7.50      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_263,c_259]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_529,plain,
% 55.11/7.50      ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_527,c_477]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_989,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK1 ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_988,c_529]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1,plain,
% 55.11/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 55.11/7.50      inference(cnf_transformation,[],[f36]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_107,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_1]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3,plain,
% 55.11/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 55.11/7.50      inference(cnf_transformation,[],[f38]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_105,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X2_38) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_3]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_449,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)),X2_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_633,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X2_38)),X3_38) = k4_xboole_0(X2_38,k4_xboole_0(X2_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X3_38))))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_449,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 55.11/7.50      inference(cnf_transformation,[],[f37]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_106,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X2_38)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38)))) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_2]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_264,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38)))) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_106,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_662,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38)))),X3_38) = k4_xboole_0(X2_38,k4_xboole_0(X2_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X3_38))))) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_633,c_105,c_264]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_102041,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_989,c_662]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_8,plain,
% 55.11/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.11/7.50      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 55.11/7.50      inference(cnf_transformation,[],[f39]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_100,plain,
% 55.11/7.50      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 55.11/7.50      | k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)) = k9_subset_1(X1_38,X2_38,X0_38) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_8]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_261,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k9_subset_1(X2_38,X0_38,X1_38)
% 55.11/7.50      | m1_subset_1(X1_38,k1_zfmisc_1(X2_38)) != iProver_top ),
% 55.11/7.50      inference(predicate_to_equality,[status(thm)],[c_100]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1861,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)) = k9_subset_1(sK0,X0_38,sK1) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_263,c_261]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_104209,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK1))) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_102041,c_1861]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_107429,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k9_subset_1(sK0,sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_104209]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2563,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,sK1)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK1))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1861,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_107823,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,sK1)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_104209,c_2563]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_642,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_449,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2562,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK1)))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK1))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1861,c_642]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_107824,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK1)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_104209,c_2562]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_611,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X2_38) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2571,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK1,X1_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1861,c_611]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1218,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38)))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_642]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6857,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK1)))) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK1,X0_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2571,c_1218]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_107861,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK1,X0_38)) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_107824,c_6857]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_624,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X2_38,X3_38))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X2_38)),X1_38),X3_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_449,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_627,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),X2_38)) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X2_38)),X1_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_449,c_107]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_667,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),X2_38)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,X1_38))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_627,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_671,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),X3_38),X2_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_624,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_672,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X3_38),X2_38))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_671,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_0,plain,
% 55.11/7.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 55.11/7.50      inference(cnf_transformation,[],[f35]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_108,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38))) = k4_xboole_0(X0_38,X1_38) ),
% 55.11/7.50      inference(subtyping,[status(esa)],[c_0]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3817,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38)))) = k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X3_38),X2_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_672,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_13154,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38)) = k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X3_38),X2_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_3817,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17091,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38)) = k4_xboole_0(X2_38,k4_xboole_0(X2_38,k4_xboole_0(X0_38,X1_38))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13154,c_107]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_21708,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,X0_38),k4_xboole_0(sK0,sK1))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_989,c_17091]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_22210,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,X0_38),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,X0_38,sK1) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_21708,c_989,c_1861]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23151,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,k4_xboole_0(sK0,X0_38),sK1) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_22210]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2591,plain,
% 55.11/7.50      ( k9_subset_1(sK0,sK0,sK1) = sK1 ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1861,c_989]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2589,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK1,X1_38))) = k9_subset_1(sK0,k4_xboole_0(X0_38,X1_38),sK1) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1861,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2596,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(X0_38,X1_38),sK1) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_2571,c_2589]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23309,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) = k4_xboole_0(sK1,X0_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_23151,c_611,c_2591,c_2596]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23310,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK1)) = k4_xboole_0(sK1,X0_38) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_23309,c_989,c_1861]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_602,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,X2_38)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3238,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X1_38,X2_38)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X1_38)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_602]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23396,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0_38)),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK1))))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_23310,c_3238]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2582,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0_38)) = k9_subset_1(sK0,X0_38,sK1) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1861,c_107]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3108,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X1_38,k4_xboole_0(sK1,X0_38)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2582,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3142,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) = k9_subset_1(sK0,k4_xboole_0(X1_38,k4_xboole_0(sK1,X0_38)),sK1) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_3108,c_2582]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3143,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK1,X0_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_3142,c_2596]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23431,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK1))))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(sK1,X1_38)) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_23396,c_2582,c_3143]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2579,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0_38,X1_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1861,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23163,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,sK0)))),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,X1_38))),sK1) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1218,c_22210]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_381,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38))) = k4_xboole_0(X0_38,X1_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_626,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X2_38)),X1_38)) = k4_xboole_0(k4_xboole_0(X0_38,X1_38),X2_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_449,c_381]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_668,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,X1_38)))) = k4_xboole_0(k4_xboole_0(X0_38,X1_38),X2_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_626,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6346,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38)))),k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X3_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38))))))) = k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)))),X3_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1218,c_668]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3381,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,X2_38)),k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X3_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38))))))) = k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38)))),X3_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_602,c_668]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2038,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))),k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(X3_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38)),X3_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_667,c_668]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2091,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X3_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38)),X2_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X3_38),X2_38))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_2038,c_611,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1970,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))),k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))),X3_38)) = k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(X3_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_667,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2001,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X3_38)),X2_38))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,k4_xboole_0(X3_38,X2_38))))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_1970,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2092,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X3_38))),X2_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_2091,c_668,c_2001]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3455,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38)))),k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X3_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38))))))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(k4_xboole_0(X2_38,X3_38),k4_xboole_0(X2_38,X0_38)))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_3381,c_611,c_2092]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6445,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),k4_xboole_0(X1_38,X3_38)))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X3_38)))),X2_38) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_6346,c_3455]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3713,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),k4_xboole_0(X1_38,X3_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X3_38,X2_38))))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_611,c_672]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6446,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38)))),X3_38) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,X3_38))))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_6445,c_2092,c_3713]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23294,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))))) = k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(sK0,X1_38))) ),
% 55.11/7.50      inference(demodulation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_23163,c_2591,c_2596,c_6446]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23295,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,sK1))))) = k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(sK0,X1_38))) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_23294,c_989]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23296,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(X0_38,k4_xboole_0(sK0,X1_38))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_23295,c_1861]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23432,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(sK0,X1_38)) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),k4_xboole_0(sK1,X1_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_23431,c_2579,c_23296]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1567,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),k4_xboole_0(sK0,sK1)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK1)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_989,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_100043,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),k4_xboole_0(sK0,sK1)) = k9_subset_1(sK0,X0_38,sK1) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_1567,c_1861]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_107862,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK0,X0_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_107861,c_23432,c_100043]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_107863,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,sK1)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),k4_xboole_0(sK0,X0_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_107823,c_107862]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_108771,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k9_subset_1(sK0,sK0,sK1))) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK0,sK0)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_107429,c_107863]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1860,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_262,c_261]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23166,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(k9_subset_1(sK0,sK0,sK2),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_22210]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_9201,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_3238]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2436,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_107]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_9751,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2))) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_9201,c_1860,c_2436]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23175,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK0,sK1))) = k9_subset_1(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)),sK1) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_9751,c_22210]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23274,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK2)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_23175,c_2591,c_2596]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23288,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK1,k9_subset_1(sK0,sK0,sK2)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_23166,c_23274]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2445,plain,
% 55.11/7.50      ( k9_subset_1(sK0,sK0,sK2) = sK2 ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_980]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23289,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK1,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_23288,c_2445]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_108772,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK0)) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_108771,c_2591,c_23289]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2422,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X0_38,sK2),X1_38))) = k4_xboole_0(k4_xboole_0(X0_38,k9_subset_1(sK0,X0_38,sK2)),X1_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_611]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2417,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),k4_xboole_0(X0_38,sK2)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2425,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK2,X1_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),X1_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_611]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_18893,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,sK2,sK2)))) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)),sK2),sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2417,c_2425]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1076,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),k4_xboole_0(sK0,sK2)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11612,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_1076,c_1860]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_13099,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,X1_38))) = k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK2)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_11612,c_3817]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_13221,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK2)))) = k4_xboole_0(X0_38,k4_xboole_0(sK2,k4_xboole_0(sK0,X1_38))) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_13099,c_980]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_13222,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(sK2,k4_xboole_0(sK0,X1_38))) = k4_xboole_0(X0_38,k9_subset_1(sK0,X1_38,sK2)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_13221,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2416,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK2)))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_642]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16446,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13222,c_2416]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2433,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0_38,X1_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),X1_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16450,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,sK0,sK2),X0_38) = k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13222,c_2433]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17284,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK2,X0_38) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_16450,c_2445]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17291,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16446,c_17284]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3310,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)),k4_xboole_0(sK2,sK0)) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_602]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3518,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK2,sK0)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_3310,c_1860,c_2436]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4339,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k9_subset_1(sK0,sK0,sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2445,c_3518]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4388,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = sK2 ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_4339,c_2445]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6213,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0_38,k4_xboole_0(sK2,sK0)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_1218]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6498,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0_38,k4_xboole_0(sK2,sK0)))) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_6213,c_1860]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_7810,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK2)))) = k9_subset_1(sK0,sK2,sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_6498,c_1218]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4745,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,sK0,sK2),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_2433]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4823,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_4745,c_2445]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4824,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,sK2,sK2) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_4823,c_2436]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_8043,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK2))) = k9_subset_1(sK0,sK2,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_7810,c_4824]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17292,plain,
% 55.11/7.50      ( k9_subset_1(sK0,sK2,sK2) = sK2 ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_17291,c_4388,c_8043]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16438,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)),sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13222,c_2436]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17303,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)),sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16438,c_17284]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16463,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK2,X0_38) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_16450,c_2445]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16470,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16446,c_16463]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16471,plain,
% 55.11/7.50      ( k9_subset_1(sK0,sK2,sK2) = sK2 ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_16470,c_4388,c_8043]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16449,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,sK2,sK2),k4_xboole_0(sK0,X0_38)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13222,c_2433]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16464,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,sK2,sK2),k4_xboole_0(sK0,X0_38)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16449,c_16463]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16465,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,sK2,sK2),k4_xboole_0(sK0,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_16464,c_2436]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16472,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16471,c_16465]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17304,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_17303,c_2436,c_16472]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_15529,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_subset_1(sK0,sK0,sK2)))),k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))),sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2416,c_11612]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11659,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)),k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)),sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_9751,c_11612]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2443,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK2,X1_38))) = k9_subset_1(sK0,k4_xboole_0(X0_38,X1_38),sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2450,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(X0_38,X1_38),sK2) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),X1_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_2425,c_2443]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11812,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_11659,c_2445,c_2450]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_15773,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))),sK2) = k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_15529,c_1860,c_2445,c_11812]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_18059,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))),sK2) = k4_xboole_0(sK2,X0_38) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_15773,c_15773,c_17284]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_388,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)))) = k4_xboole_0(k4_xboole_0(X0_38,X1_38),X0_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_381]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2432,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(sK2,X0_38),k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(k4_xboole_0(sK2,X0_38),sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_388]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_18080,plain,
% 55.11/7.50      ( k5_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))),k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))),sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_18059,c_2432]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2435,plain,
% 55.11/7.50      ( k5_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK2,X0_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_381]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_18084,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k5_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_18059,c_2435]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11689,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0_38)),sK2),k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_11612,c_2433]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4733,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))))) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),sK2),X2_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_611,c_2433]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4831,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)),sK2),X2_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_4733,c_2433]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4832,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,X1_38)),X2_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_4831,c_2450]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11755,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2) ),
% 55.11/7.50      inference(demodulation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_11689,c_2436,c_2450,c_4832]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11756,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_11755,c_2445]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16400,plain,
% 55.11/7.50      ( k5_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13222,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17351,plain,
% 55.11/7.50      ( k5_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) = k4_xboole_0(sK2,k4_xboole_0(sK0,X0_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16400,c_17284]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17352,plain,
% 55.11/7.50      ( k5_xboole_0(sK2,k4_xboole_0(sK2,X0_38)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_17351,c_16472]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_18088,plain,
% 55.11/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_18084,c_11756,c_17352]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_18092,plain,
% 55.11/7.50      ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK2,k4_xboole_0(sK2,X0_38))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK2) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_18080,c_18088]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_10071,plain,
% 55.11/7.50      ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_9751,c_381]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_18093,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK2) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_18092,c_2436,c_10071]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_19113,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_18893,c_1860,c_2436,c_17292,c_17304,c_18093]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_621,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)),X2_38)) = k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_449,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_674,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_621,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2411,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k9_subset_1(sK0,X0_38,sK2)))) = k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_674]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_19889,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0))) = k4_xboole_0(X0_38,k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_19113,c_2411]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_2427,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(X0_38,sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4747,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k9_subset_1(sK0,X0_38,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1860,c_2433]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4820,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(X0_38,sK2)) = k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_4747,c_2436]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_383,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_10070,plain,
% 55.11/7.50      ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_9751,c_383]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4363,plain,
% 55.11/7.50      ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(sK2,sK0)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_3518,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_4370,plain,
% 55.11/7.50      ( k5_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k9_subset_1(sK0,X0_38,sK2))) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_4363,c_3518]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_10079,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),k4_xboole_0(k9_subset_1(sK0,X0_38,sK2),sK0)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_10070,c_4370]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_19895,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK2),sK2)) = k4_xboole_0(X0_38,sK2) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_19889,c_2427,c_4820,c_10079]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_19896,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(X0_38,sK2) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_19895,c_17304]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_20163,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X0_38,sK2),X1_38))) = k4_xboole_0(k4_xboole_0(X0_38,sK2),X1_38) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_2422,c_2422,c_19896]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_50570,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k9_subset_1(sK0,X0_38,sK1))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X0_38)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_23296,c_20163]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6840,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,X0_38),X1_38)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2571,c_107]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23411,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK1),sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_23310,c_2582]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_23416,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k9_subset_1(sK0,X0_38,sK1),sK1) = k9_subset_1(sK0,X0_38,sK1) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_23411,c_2582]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_13137,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X2_38)))) = k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(sK1,X2_38),k4_xboole_0(sK1,X1_38))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2582,c_3817]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_13181,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(sK1,X1_38),k4_xboole_0(sK1,X2_38))) = k4_xboole_0(X0_38,k4_xboole_0(k9_subset_1(sK0,X2_38,sK1),X1_38)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_13137,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_25070,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,X1_38),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13181,c_17091]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_25084,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38)) = k4_xboole_0(k9_subset_1(sK0,k4_xboole_0(sK1,X0_38),sK1),X1_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13181,c_2571]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_3134,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(sK1,X0_38),sK1) = k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK1)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2582,c_2582]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_21597,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(sK1,X1_38))) = k4_xboole_0(k4_xboole_0(sK1,X1_38),k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),X1_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2582,c_17091]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6837,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(X1_38,X2_38))) = k4_xboole_0(k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38),X2_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2571,c_449]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6876,plain,
% 55.11/7.50      ( k9_subset_1(sK0,k4_xboole_0(sK1,X0_38),sK1) = k4_xboole_0(k9_subset_1(sK0,sK1,sK1),X0_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_2571,c_2582]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_6893,plain,
% 55.11/7.50      ( k4_xboole_0(k9_subset_1(sK0,sK1,sK1),X0_38) = k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK1)) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_6876,c_3134]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_22294,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,k9_subset_1(sK0,X1_38,sK1)),X0_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_21597,c_6837,c_6893]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_25123,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,k9_subset_1(sK0,X0_38,sK1)),X1_38) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_25084,c_3134,c_22294]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_25124,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,X0_38),X1_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_25123,c_22294,c_23310]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_25142,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)),X0_38)) = k4_xboole_0(k4_xboole_0(sK1,X1_38),X0_38) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_25070,c_25124]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_17171,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,X0_38),k4_xboole_0(k4_xboole_0(sK1,X1_38),X0_38)) = k4_xboole_0(k9_subset_1(sK0,X1_38,sK1),X0_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_13154,c_6840]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_21522,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,X2_38))) = k4_xboole_0(k4_xboole_0(X0_38,X2_38),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_611,c_17091]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_620,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)),X2_38),X3_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_449,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_675,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,X2_38),X3_38))) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X3_38))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_620,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_5464,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0_38,X1_38),X1_38),X2_38))) = k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,X1_38)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_667,c_675]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_5640,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X2_38,X3_38))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X2_38,X1_38),X3_38))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_675,c_642]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_22358,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,X1_38),k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X2_38,X1_38)))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X0_38,X2_38),X1_38))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_21522,c_5464,c_5640]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_25143,plain,
% 55.11/7.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,X0_38),X1_38))) = k4_xboole_0(k4_xboole_0(sK1,X0_38),X1_38) ),
% 55.11/7.50      inference(demodulation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_25142,c_611,c_17171,c_22358]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_50586,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X0_38)) = k4_xboole_0(k9_subset_1(sK0,X0_38,sK1),sK2) ),
% 55.11/7.50      inference(demodulation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_50570,c_6840,c_23416,c_25143]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1370,plain,
% 55.11/7.50      ( k5_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK2))) = k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_674]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_619,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)),X2_38))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_449,c_108]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_676,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38))))) = k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(X1_38,X2_38))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_619,c_105]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_10073,plain,
% 55.11/7.50      ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_9751,c_676]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_10078,plain,
% 55.11/7.50      ( k5_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_10073,c_9751]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_58676,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,sK2)) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_1370,c_1370,c_1860,c_10078]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_58740,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,k9_subset_1(sK0,sK0,sK2)),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_58676,c_3238]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1863,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) = k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_974,c_261]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11621,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k4_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X0_38,sK2) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_11612]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11964,plain,
% 55.11/7.50      ( k5_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k9_subset_1(sK0,X0_38,sK2))) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_11621,c_674]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11965,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),sK2))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k9_subset_1(sK0,X0_38,sK2)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_11621,c_642]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11988,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) = k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k9_subset_1(sK0,X0_38,sK2)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_11965,c_611]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_9234,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_3238]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_9735,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_9234,c_1863]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_9736,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_9735,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11989,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),k9_subset_1(sK0,X0_38,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) ),
% 55.11/7.50      inference(light_normalisation,
% 55.11/7.50                [status(thm)],
% 55.11/7.50                [c_11988,c_1863,c_9736]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11990,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X0_38,k4_xboole_0(X0_38,sK0)),sK2)) = k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2)))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_11964,c_11989]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11991,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_11990,c_108,c_611]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_11992,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2)) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_11991,c_1863]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1077,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38))) = k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_980,c_611]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_1367,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X0_38))))) = k4_xboole_0(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X0_38,X2_38))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_107,c_674]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16174,plain,
% 55.11/7.50      ( k5_xboole_0(X0_38,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38))) = k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1077,c_1367]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16190,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)))) = k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2)) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16174,c_381]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16175,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) ),
% 55.11/7.50      inference(superposition,[status(thm)],[c_1077,c_1218]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16189,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16175,c_667]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16191,plain,
% 55.11/7.50      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) ),
% 55.11/7.50      inference(demodulation,[status(thm)],[c_16190,c_16189]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_16192,plain,
% 55.11/7.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0_38,sK2))) = k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)) ),
% 55.11/7.50      inference(light_normalisation,[status(thm)],[c_16191,c_1863]) ).
% 55.11/7.50  
% 55.11/7.50  cnf(c_58823,plain,
% 55.11/7.50      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),X0_38)) = k9_subset_1(sK0,X0_38,k4_xboole_0(sK0,sK2)) ),
% 55.11/7.51      inference(light_normalisation,
% 55.11/7.51                [status(thm)],
% 55.11/7.51                [c_58740,c_1863,c_2445,c_11992,c_16192]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_108773,plain,
% 55.11/7.51      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
% 55.11/7.51      inference(demodulation,
% 55.11/7.51                [status(thm)],
% 55.11/7.51                [c_108772,c_2591,c_50586,c_58823]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_7,plain,
% 55.11/7.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.11/7.51      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 55.11/7.51      inference(cnf_transformation,[],[f30]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_101,plain,
% 55.11/7.51      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X1_38))
% 55.11/7.51      | k7_subset_1(X1_38,X0_38,X2_38) = k4_xboole_0(X0_38,X2_38) ),
% 55.11/7.51      inference(subtyping,[status(esa)],[c_7]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_260,plain,
% 55.11/7.51      ( k7_subset_1(X0_38,X1_38,X2_38) = k4_xboole_0(X1_38,X2_38)
% 55.11/7.51      | m1_subset_1(X1_38,k1_zfmisc_1(X0_38)) != iProver_top ),
% 55.11/7.51      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_1094,plain,
% 55.11/7.51      ( k7_subset_1(sK0,sK1,X0_38) = k4_xboole_0(sK1,X0_38) ),
% 55.11/7.51      inference(superposition,[status(thm)],[c_263,c_260]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_9,negated_conjecture,
% 55.11/7.51      ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
% 55.11/7.51      inference(cnf_transformation,[],[f34]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_99,negated_conjecture,
% 55.11/7.51      ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
% 55.11/7.51      inference(subtyping,[status(esa)],[c_9]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_783,plain,
% 55.11/7.51      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k7_subset_1(sK0,sK1,sK2) ),
% 55.11/7.51      inference(demodulation,[status(thm)],[c_476,c_99]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(c_1493,plain,
% 55.11/7.51      ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) ),
% 55.11/7.51      inference(demodulation,[status(thm)],[c_1094,c_783]) ).
% 55.11/7.51  
% 55.11/7.51  cnf(contradiction,plain,
% 55.11/7.51      ( $false ),
% 55.11/7.51      inference(minisat,[status(thm)],[c_108773,c_1493]) ).
% 55.11/7.51  
% 55.11/7.51  
% 55.11/7.51  % SZS output end CNFRefutation for theBenchmark.p
% 55.11/7.51  
% 55.11/7.51  ------                               Statistics
% 55.11/7.51  
% 55.11/7.51  ------ General
% 55.11/7.51  
% 55.11/7.51  abstr_ref_over_cycles:                  0
% 55.11/7.51  abstr_ref_under_cycles:                 0
% 55.11/7.51  gc_basic_clause_elim:                   0
% 55.11/7.51  forced_gc_time:                         0
% 55.11/7.51  parsing_time:                           0.008
% 55.11/7.51  unif_index_cands_time:                  0.
% 55.11/7.51  unif_index_add_time:                    0.
% 55.11/7.51  orderings_time:                         0.
% 55.11/7.51  out_proof_time:                         0.019
% 55.11/7.51  total_time:                             6.643
% 55.11/7.51  num_of_symbols:                         43
% 55.11/7.51  num_of_terms:                           369008
% 55.11/7.51  
% 55.11/7.51  ------ Preprocessing
% 55.11/7.51  
% 55.11/7.51  num_of_splits:                          0
% 55.11/7.51  num_of_split_atoms:                     0
% 55.11/7.51  num_of_reused_defs:                     0
% 55.11/7.51  num_eq_ax_congr_red:                    2
% 55.11/7.51  num_of_sem_filtered_clauses:            1
% 55.11/7.51  num_of_subtypes:                        2
% 55.11/7.51  monotx_restored_types:                  0
% 55.11/7.51  sat_num_of_epr_types:                   0
% 55.11/7.51  sat_num_of_non_cyclic_types:            0
% 55.11/7.51  sat_guarded_non_collapsed_types:        1
% 55.11/7.51  num_pure_diseq_elim:                    0
% 55.11/7.51  simp_replaced_by:                       0
% 55.11/7.51  res_preprocessed:                       57
% 55.11/7.51  prep_upred:                             0
% 55.11/7.51  prep_unflattend:                        0
% 55.11/7.51  smt_new_axioms:                         0
% 55.11/7.51  pred_elim_cands:                        1
% 55.11/7.51  pred_elim:                              0
% 55.11/7.51  pred_elim_cl:                           0
% 55.11/7.51  pred_elim_cycles:                       1
% 55.11/7.51  merged_defs:                            0
% 55.11/7.51  merged_defs_ncl:                        0
% 55.11/7.51  bin_hyper_res:                          0
% 55.11/7.51  prep_cycles:                            3
% 55.11/7.51  pred_elim_time:                         0.
% 55.11/7.51  splitting_time:                         0.
% 55.11/7.51  sem_filter_time:                        0.
% 55.11/7.51  monotx_time:                            0.
% 55.11/7.51  subtype_inf_time:                       0.
% 55.11/7.51  
% 55.11/7.51  ------ Problem properties
% 55.11/7.51  
% 55.11/7.51  clauses:                                12
% 55.11/7.51  conjectures:                            3
% 55.11/7.51  epr:                                    0
% 55.11/7.51  horn:                                   12
% 55.11/7.51  ground:                                 3
% 55.11/7.51  unary:                                  7
% 55.11/7.51  binary:                                 5
% 55.11/7.51  lits:                                   17
% 55.11/7.51  lits_eq:                                9
% 55.11/7.51  fd_pure:                                0
% 55.11/7.51  fd_pseudo:                              0
% 55.11/7.51  fd_cond:                                0
% 55.11/7.51  fd_pseudo_cond:                         0
% 55.11/7.51  ac_symbols:                             0
% 55.11/7.51  
% 55.11/7.51  ------ Propositional Solver
% 55.11/7.51  
% 55.11/7.51  prop_solver_calls:                      33
% 55.11/7.51  prop_fast_solver_calls:                 552
% 55.11/7.51  smt_solver_calls:                       0
% 55.11/7.51  smt_fast_solver_calls:                  0
% 55.11/7.51  prop_num_of_clauses:                    27329
% 55.11/7.51  prop_preprocess_simplified:             14621
% 55.11/7.51  prop_fo_subsumed:                       2
% 55.11/7.51  prop_solver_time:                       0.
% 55.11/7.51  smt_solver_time:                        0.
% 55.11/7.51  smt_fast_solver_time:                   0.
% 55.11/7.51  prop_fast_solver_time:                  0.
% 55.11/7.51  prop_unsat_core_time:                   0.003
% 55.11/7.51  
% 55.11/7.51  ------ QBF
% 55.11/7.51  
% 55.11/7.51  qbf_q_res:                              0
% 55.11/7.51  qbf_num_tautologies:                    0
% 55.11/7.51  qbf_prep_cycles:                        0
% 55.11/7.51  
% 55.11/7.51  ------ BMC1
% 55.11/7.51  
% 55.11/7.51  bmc1_current_bound:                     -1
% 55.11/7.51  bmc1_last_solved_bound:                 -1
% 55.11/7.51  bmc1_unsat_core_size:                   -1
% 55.11/7.51  bmc1_unsat_core_parents_size:           -1
% 55.11/7.51  bmc1_merge_next_fun:                    0
% 55.11/7.51  bmc1_unsat_core_clauses_time:           0.
% 55.11/7.51  
% 55.11/7.51  ------ Instantiation
% 55.11/7.51  
% 55.11/7.51  inst_num_of_clauses:                    2587
% 55.11/7.51  inst_num_in_passive:                    448
% 55.11/7.51  inst_num_in_active:                     1161
% 55.11/7.51  inst_num_in_unprocessed:                978
% 55.11/7.51  inst_num_of_loops:                      1190
% 55.11/7.51  inst_num_of_learning_restarts:          0
% 55.11/7.51  inst_num_moves_active_passive:          22
% 55.11/7.51  inst_lit_activity:                      0
% 55.11/7.51  inst_lit_activity_moves:                0
% 55.11/7.51  inst_num_tautologies:                   0
% 55.11/7.51  inst_num_prop_implied:                  0
% 55.11/7.51  inst_num_existing_simplified:           0
% 55.11/7.51  inst_num_eq_res_simplified:             0
% 55.11/7.51  inst_num_child_elim:                    0
% 55.11/7.51  inst_num_of_dismatching_blockings:      1083
% 55.11/7.51  inst_num_of_non_proper_insts:           4146
% 55.11/7.51  inst_num_of_duplicates:                 0
% 55.11/7.51  inst_inst_num_from_inst_to_res:         0
% 55.11/7.51  inst_dismatching_checking_time:         0.
% 55.11/7.51  
% 55.11/7.51  ------ Resolution
% 55.11/7.51  
% 55.11/7.51  res_num_of_clauses:                     0
% 55.11/7.51  res_num_in_passive:                     0
% 55.11/7.51  res_num_in_active:                      0
% 55.11/7.51  res_num_of_loops:                       60
% 55.11/7.51  res_forward_subset_subsumed:            534
% 55.11/7.51  res_backward_subset_subsumed:           0
% 55.11/7.51  res_forward_subsumed:                   0
% 55.11/7.51  res_backward_subsumed:                  0
% 55.11/7.51  res_forward_subsumption_resolution:     0
% 55.11/7.51  res_backward_subsumption_resolution:    0
% 55.11/7.51  res_clause_to_clause_subsumption:       446802
% 55.11/7.51  res_orphan_elimination:                 0
% 55.11/7.51  res_tautology_del:                      388
% 55.11/7.51  res_num_eq_res_simplified:              0
% 55.11/7.51  res_num_sel_changes:                    0
% 55.11/7.51  res_moves_from_active_to_pass:          0
% 55.11/7.51  
% 55.11/7.51  ------ Superposition
% 55.11/7.51  
% 55.11/7.51  sup_time_total:                         0.
% 55.11/7.51  sup_time_generating:                    0.
% 55.11/7.51  sup_time_sim_full:                      0.
% 55.11/7.51  sup_time_sim_immed:                     0.
% 55.11/7.51  
% 55.11/7.51  sup_num_of_clauses:                     13592
% 55.11/7.51  sup_num_in_active:                      203
% 55.11/7.51  sup_num_in_passive:                     13389
% 55.11/7.51  sup_num_of_loops:                       237
% 55.11/7.51  sup_fw_superposition:                   17175
% 55.11/7.51  sup_bw_superposition:                   18793
% 55.11/7.51  sup_immediate_simplified:               29829
% 55.11/7.51  sup_given_eliminated:                   14
% 55.11/7.51  comparisons_done:                       0
% 55.11/7.51  comparisons_avoided:                    0
% 55.11/7.51  
% 55.11/7.51  ------ Simplifications
% 55.11/7.51  
% 55.11/7.51  
% 55.11/7.51  sim_fw_subset_subsumed:                 2
% 55.11/7.51  sim_bw_subset_subsumed:                 0
% 55.11/7.51  sim_fw_subsumed:                        1251
% 55.11/7.51  sim_bw_subsumed:                        271
% 55.11/7.51  sim_fw_subsumption_res:                 0
% 55.11/7.51  sim_bw_subsumption_res:                 0
% 55.11/7.51  sim_tautology_del:                      0
% 55.11/7.51  sim_eq_tautology_del:                   6011
% 55.11/7.51  sim_eq_res_simp:                        0
% 55.11/7.51  sim_fw_demodulated:                     32807
% 55.11/7.51  sim_bw_demodulated:                     1373
% 55.11/7.51  sim_light_normalised:                   15039
% 55.11/7.51  sim_joinable_taut:                      0
% 55.11/7.51  sim_joinable_simp:                      0
% 55.11/7.51  sim_ac_normalised:                      0
% 55.11/7.51  sim_smt_subsumption:                    0
% 55.11/7.51  
%------------------------------------------------------------------------------
