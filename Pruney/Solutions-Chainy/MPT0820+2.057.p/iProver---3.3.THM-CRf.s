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
% DateTime   : Thu Dec  3 11:55:01 EST 2020

% Result     : Theorem 11.55s
% Output     : CNFRefutation 11.55s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 188 expanded)
%              Number of clauses        :   76 (  92 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  262 ( 378 expanded)
%              Number of equality atoms :   76 (  92 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f35])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f46,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f46,f35])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X1_43,X2_43)
    | r1_tarski(X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1103,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X1_43,k3_tarski(k2_tarski(sK0,sK1)))
    | r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_43398,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),X0_43)
    | r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_43403,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_43398])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X0_43,k3_tarski(k2_tarski(X2_43,X1_43))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1106,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(X0_43,sK1) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_14885,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_214,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X1_43)
    | r1_tarski(k3_tarski(k2_tarski(X0_43,X2_43)),X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1717,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(X1_43,k3_tarski(k2_tarski(sK0,sK1)))
    | r1_tarski(k3_tarski(k2_tarski(X0_43,X1_43)),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_11276,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1717])).

cnf(c_225,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_1457,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,k3_tarski(k2_tarski(X3_43,X4_43)))
    | X0_43 != X2_43
    | X1_43 != k3_tarski(k2_tarski(X3_43,X4_43)) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_2194,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43)))
    | r1_tarski(X3_43,k3_tarski(k2_tarski(X1_43,X2_43)))
    | X3_43 != X0_43
    | k3_tarski(k2_tarski(X1_43,X2_43)) != k3_tarski(k2_tarski(X1_43,X2_43)) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_4266,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
    | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | k3_relat_1(sK2) != X0_43
    | k3_tarski(k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_11169,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1)))
    | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
    | k3_tarski(k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4266])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_210,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_608,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_204,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_614,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_204])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_212,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_606,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_940,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_606])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_120,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_121,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_120])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_121])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ v1_relat_1(X1_43)
    | v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_146])).

cnf(c_615,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_2477,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_940,c_615])).

cnf(c_2951,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_608,c_2477])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | k2_relset_1(X1_43,X2_43,X0_43) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_612,plain,
    ( k2_relset_1(X0_43,X1_43,X2_43) = k2_relat_1(X2_43)
    | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_1214,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_614,c_612])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_610,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_1779,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_610])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1999,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1779,c_15])).

cnf(c_2003,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1999,c_606])).

cnf(c_2004,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2003])).

cnf(c_219,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1604,plain,
    ( k3_tarski(k2_tarski(sK0,sK1)) = k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_207,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | k1_relset_1(X1_43,X2_43,X0_43) = k1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_611,plain,
    ( k1_relset_1(X0_43,X1_43,X2_43) = k1_relat_1(X2_43)
    | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_1208,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_614,c_611])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | m1_subset_1(k1_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X1_43)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_609,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_1438,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_609])).

cnf(c_1529,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1438,c_15])).

cnf(c_1533,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_606])).

cnf(c_1534,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1533])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_211,plain,
    ( ~ v1_relat_1(X0_43)
    | k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1500,plain,
    ( ~ v1_relat_1(sK2)
    | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_1501,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_215,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,X1_43))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1440,plain,
    ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_222,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_709,plain,
    ( X0_43 != X1_43
    | k3_relat_1(sK2) != X1_43
    | k3_relat_1(sK2) = X0_43 ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_820,plain,
    ( X0_43 != k3_relat_1(sK2)
    | k3_relat_1(sK2) = X0_43
    | k3_relat_1(sK2) != k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_1028,plain,
    ( k3_relat_1(sK2) != k3_relat_1(sK2)
    | k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
    | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) != k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_808,plain,
    ( k3_relat_1(sK2) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43403,c_14885,c_11276,c_11169,c_2951,c_2004,c_1604,c_1534,c_1501,c_1440,c_1028,c_808,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.55/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.55/1.99  
% 11.55/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.55/1.99  
% 11.55/1.99  ------  iProver source info
% 11.55/1.99  
% 11.55/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.55/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.55/1.99  git: non_committed_changes: false
% 11.55/1.99  git: last_make_outside_of_git: false
% 11.55/1.99  
% 11.55/1.99  ------ 
% 11.55/1.99  
% 11.55/1.99  ------ Input Options
% 11.55/1.99  
% 11.55/1.99  --out_options                           all
% 11.55/1.99  --tptp_safe_out                         true
% 11.55/1.99  --problem_path                          ""
% 11.55/1.99  --include_path                          ""
% 11.55/1.99  --clausifier                            res/vclausify_rel
% 11.55/1.99  --clausifier_options                    ""
% 11.55/1.99  --stdin                                 false
% 11.55/1.99  --stats_out                             all
% 11.55/1.99  
% 11.55/1.99  ------ General Options
% 11.55/1.99  
% 11.55/1.99  --fof                                   false
% 11.55/1.99  --time_out_real                         305.
% 11.55/1.99  --time_out_virtual                      -1.
% 11.55/1.99  --symbol_type_check                     false
% 11.55/1.99  --clausify_out                          false
% 11.55/1.99  --sig_cnt_out                           false
% 11.55/1.99  --trig_cnt_out                          false
% 11.55/1.99  --trig_cnt_out_tolerance                1.
% 11.55/1.99  --trig_cnt_out_sk_spl                   false
% 11.55/1.99  --abstr_cl_out                          false
% 11.55/1.99  
% 11.55/1.99  ------ Global Options
% 11.55/1.99  
% 11.55/1.99  --schedule                              default
% 11.55/1.99  --add_important_lit                     false
% 11.55/1.99  --prop_solver_per_cl                    1000
% 11.55/1.99  --min_unsat_core                        false
% 11.55/1.99  --soft_assumptions                      false
% 11.55/1.99  --soft_lemma_size                       3
% 11.55/1.99  --prop_impl_unit_size                   0
% 11.55/1.99  --prop_impl_unit                        []
% 11.55/1.99  --share_sel_clauses                     true
% 11.55/1.99  --reset_solvers                         false
% 11.55/1.99  --bc_imp_inh                            [conj_cone]
% 11.55/1.99  --conj_cone_tolerance                   3.
% 11.55/1.99  --extra_neg_conj                        none
% 11.55/1.99  --large_theory_mode                     true
% 11.55/1.99  --prolific_symb_bound                   200
% 11.55/1.99  --lt_threshold                          2000
% 11.55/1.99  --clause_weak_htbl                      true
% 11.55/1.99  --gc_record_bc_elim                     false
% 11.55/1.99  
% 11.55/1.99  ------ Preprocessing Options
% 11.55/1.99  
% 11.55/1.99  --preprocessing_flag                    true
% 11.55/1.99  --time_out_prep_mult                    0.1
% 11.55/1.99  --splitting_mode                        input
% 11.55/1.99  --splitting_grd                         true
% 11.55/1.99  --splitting_cvd                         false
% 11.55/1.99  --splitting_cvd_svl                     false
% 11.55/1.99  --splitting_nvd                         32
% 11.55/1.99  --sub_typing                            true
% 11.55/1.99  --prep_gs_sim                           true
% 11.55/1.99  --prep_unflatten                        true
% 11.55/1.99  --prep_res_sim                          true
% 11.55/1.99  --prep_upred                            true
% 11.55/1.99  --prep_sem_filter                       exhaustive
% 11.55/1.99  --prep_sem_filter_out                   false
% 11.55/1.99  --pred_elim                             true
% 11.55/1.99  --res_sim_input                         true
% 11.55/1.99  --eq_ax_congr_red                       true
% 11.55/1.99  --pure_diseq_elim                       true
% 11.55/1.99  --brand_transform                       false
% 11.55/1.99  --non_eq_to_eq                          false
% 11.55/1.99  --prep_def_merge                        true
% 11.55/1.99  --prep_def_merge_prop_impl              false
% 11.55/1.99  --prep_def_merge_mbd                    true
% 11.55/1.99  --prep_def_merge_tr_red                 false
% 11.55/1.99  --prep_def_merge_tr_cl                  false
% 11.55/1.99  --smt_preprocessing                     true
% 11.55/1.99  --smt_ac_axioms                         fast
% 11.55/1.99  --preprocessed_out                      false
% 11.55/1.99  --preprocessed_stats                    false
% 11.55/1.99  
% 11.55/1.99  ------ Abstraction refinement Options
% 11.55/1.99  
% 11.55/1.99  --abstr_ref                             []
% 11.55/1.99  --abstr_ref_prep                        false
% 11.55/1.99  --abstr_ref_until_sat                   false
% 11.55/1.99  --abstr_ref_sig_restrict                funpre
% 11.55/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.55/1.99  --abstr_ref_under                       []
% 11.55/1.99  
% 11.55/1.99  ------ SAT Options
% 11.55/1.99  
% 11.55/1.99  --sat_mode                              false
% 11.55/1.99  --sat_fm_restart_options                ""
% 11.55/1.99  --sat_gr_def                            false
% 11.55/1.99  --sat_epr_types                         true
% 11.55/1.99  --sat_non_cyclic_types                  false
% 11.55/1.99  --sat_finite_models                     false
% 11.55/1.99  --sat_fm_lemmas                         false
% 11.55/1.99  --sat_fm_prep                           false
% 11.55/1.99  --sat_fm_uc_incr                        true
% 11.55/1.99  --sat_out_model                         small
% 11.55/1.99  --sat_out_clauses                       false
% 11.55/1.99  
% 11.55/1.99  ------ QBF Options
% 11.55/1.99  
% 11.55/1.99  --qbf_mode                              false
% 11.55/1.99  --qbf_elim_univ                         false
% 11.55/1.99  --qbf_dom_inst                          none
% 11.55/1.99  --qbf_dom_pre_inst                      false
% 11.55/1.99  --qbf_sk_in                             false
% 11.55/1.99  --qbf_pred_elim                         true
% 11.55/1.99  --qbf_split                             512
% 11.55/1.99  
% 11.55/1.99  ------ BMC1 Options
% 11.55/1.99  
% 11.55/1.99  --bmc1_incremental                      false
% 11.55/1.99  --bmc1_axioms                           reachable_all
% 11.55/1.99  --bmc1_min_bound                        0
% 11.55/1.99  --bmc1_max_bound                        -1
% 11.55/1.99  --bmc1_max_bound_default                -1
% 11.55/1.99  --bmc1_symbol_reachability              true
% 11.55/1.99  --bmc1_property_lemmas                  false
% 11.55/1.99  --bmc1_k_induction                      false
% 11.55/1.99  --bmc1_non_equiv_states                 false
% 11.55/1.99  --bmc1_deadlock                         false
% 11.55/1.99  --bmc1_ucm                              false
% 11.55/1.99  --bmc1_add_unsat_core                   none
% 11.55/1.99  --bmc1_unsat_core_children              false
% 11.55/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.55/1.99  --bmc1_out_stat                         full
% 11.55/1.99  --bmc1_ground_init                      false
% 11.55/1.99  --bmc1_pre_inst_next_state              false
% 11.55/1.99  --bmc1_pre_inst_state                   false
% 11.55/1.99  --bmc1_pre_inst_reach_state             false
% 11.55/1.99  --bmc1_out_unsat_core                   false
% 11.55/1.99  --bmc1_aig_witness_out                  false
% 11.55/1.99  --bmc1_verbose                          false
% 11.55/1.99  --bmc1_dump_clauses_tptp                false
% 11.55/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.55/1.99  --bmc1_dump_file                        -
% 11.55/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.55/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.55/1.99  --bmc1_ucm_extend_mode                  1
% 11.55/1.99  --bmc1_ucm_init_mode                    2
% 11.55/1.99  --bmc1_ucm_cone_mode                    none
% 11.55/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.55/1.99  --bmc1_ucm_relax_model                  4
% 11.55/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.55/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.55/1.99  --bmc1_ucm_layered_model                none
% 11.55/1.99  --bmc1_ucm_max_lemma_size               10
% 11.55/1.99  
% 11.55/1.99  ------ AIG Options
% 11.55/1.99  
% 11.55/1.99  --aig_mode                              false
% 11.55/1.99  
% 11.55/1.99  ------ Instantiation Options
% 11.55/1.99  
% 11.55/1.99  --instantiation_flag                    true
% 11.55/1.99  --inst_sos_flag                         true
% 11.55/1.99  --inst_sos_phase                        true
% 11.55/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.55/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.55/1.99  --inst_lit_sel_side                     num_symb
% 11.55/1.99  --inst_solver_per_active                1400
% 11.55/1.99  --inst_solver_calls_frac                1.
% 11.55/1.99  --inst_passive_queue_type               priority_queues
% 11.55/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.55/1.99  --inst_passive_queues_freq              [25;2]
% 11.55/1.99  --inst_dismatching                      true
% 11.55/1.99  --inst_eager_unprocessed_to_passive     true
% 11.55/1.99  --inst_prop_sim_given                   true
% 11.55/1.99  --inst_prop_sim_new                     false
% 11.55/1.99  --inst_subs_new                         false
% 11.55/1.99  --inst_eq_res_simp                      false
% 11.55/1.99  --inst_subs_given                       false
% 11.55/1.99  --inst_orphan_elimination               true
% 11.55/1.99  --inst_learning_loop_flag               true
% 11.55/1.99  --inst_learning_start                   3000
% 11.55/1.99  --inst_learning_factor                  2
% 11.55/1.99  --inst_start_prop_sim_after_learn       3
% 11.55/1.99  --inst_sel_renew                        solver
% 11.55/1.99  --inst_lit_activity_flag                true
% 11.55/1.99  --inst_restr_to_given                   false
% 11.55/1.99  --inst_activity_threshold               500
% 11.55/1.99  --inst_out_proof                        true
% 11.55/1.99  
% 11.55/1.99  ------ Resolution Options
% 11.55/1.99  
% 11.55/1.99  --resolution_flag                       true
% 11.55/1.99  --res_lit_sel                           adaptive
% 11.55/1.99  --res_lit_sel_side                      none
% 11.55/1.99  --res_ordering                          kbo
% 11.55/1.99  --res_to_prop_solver                    active
% 11.55/1.99  --res_prop_simpl_new                    false
% 11.55/1.99  --res_prop_simpl_given                  true
% 11.55/1.99  --res_passive_queue_type                priority_queues
% 11.55/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.55/1.99  --res_passive_queues_freq               [15;5]
% 11.55/1.99  --res_forward_subs                      full
% 11.55/1.99  --res_backward_subs                     full
% 11.55/1.99  --res_forward_subs_resolution           true
% 11.55/1.99  --res_backward_subs_resolution          true
% 11.55/1.99  --res_orphan_elimination                true
% 11.55/1.99  --res_time_limit                        2.
% 11.55/1.99  --res_out_proof                         true
% 11.55/1.99  
% 11.55/1.99  ------ Superposition Options
% 11.55/1.99  
% 11.55/1.99  --superposition_flag                    true
% 11.55/1.99  --sup_passive_queue_type                priority_queues
% 11.55/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.55/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.55/1.99  --demod_completeness_check              fast
% 11.55/1.99  --demod_use_ground                      true
% 11.55/1.99  --sup_to_prop_solver                    passive
% 11.55/1.99  --sup_prop_simpl_new                    true
% 11.55/1.99  --sup_prop_simpl_given                  true
% 11.55/1.99  --sup_fun_splitting                     true
% 11.55/1.99  --sup_smt_interval                      50000
% 11.55/1.99  
% 11.55/1.99  ------ Superposition Simplification Setup
% 11.55/1.99  
% 11.55/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.55/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.55/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.55/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.55/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.55/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.55/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.55/1.99  --sup_immed_triv                        [TrivRules]
% 11.55/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/1.99  --sup_immed_bw_main                     []
% 11.55/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.55/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.55/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/1.99  --sup_input_bw                          []
% 11.55/1.99  
% 11.55/1.99  ------ Combination Options
% 11.55/1.99  
% 11.55/1.99  --comb_res_mult                         3
% 11.55/1.99  --comb_sup_mult                         2
% 11.55/1.99  --comb_inst_mult                        10
% 11.55/1.99  
% 11.55/1.99  ------ Debug Options
% 11.55/1.99  
% 11.55/1.99  --dbg_backtrace                         false
% 11.55/1.99  --dbg_dump_prop_clauses                 false
% 11.55/1.99  --dbg_dump_prop_clauses_file            -
% 11.55/1.99  --dbg_out_stat                          false
% 11.55/1.99  ------ Parsing...
% 11.55/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.55/1.99  
% 11.55/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.55/1.99  
% 11.55/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.55/1.99  
% 11.55/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.55/1.99  ------ Proving...
% 11.55/1.99  ------ Problem Properties 
% 11.55/1.99  
% 11.55/1.99  
% 11.55/1.99  clauses                                 15
% 11.55/1.99  conjectures                             2
% 11.55/1.99  EPR                                     2
% 11.55/1.99  Horn                                    15
% 11.55/1.99  unary                                   4
% 11.55/1.99  binary                                  8
% 11.55/1.99  lits                                    29
% 11.55/1.99  lits eq                                 3
% 11.55/1.99  fd_pure                                 0
% 11.55/1.99  fd_pseudo                               0
% 11.55/1.99  fd_cond                                 0
% 11.55/1.99  fd_pseudo_cond                          0
% 11.55/1.99  AC symbols                              0
% 11.55/1.99  
% 11.55/1.99  ------ Schedule dynamic 5 is on 
% 11.55/1.99  
% 11.55/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.55/1.99  
% 11.55/1.99  
% 11.55/1.99  ------ 
% 11.55/1.99  Current options:
% 11.55/1.99  ------ 
% 11.55/1.99  
% 11.55/1.99  ------ Input Options
% 11.55/1.99  
% 11.55/1.99  --out_options                           all
% 11.55/1.99  --tptp_safe_out                         true
% 11.55/1.99  --problem_path                          ""
% 11.55/1.99  --include_path                          ""
% 11.55/1.99  --clausifier                            res/vclausify_rel
% 11.55/1.99  --clausifier_options                    ""
% 11.55/1.99  --stdin                                 false
% 11.55/1.99  --stats_out                             all
% 11.55/1.99  
% 11.55/1.99  ------ General Options
% 11.55/1.99  
% 11.55/1.99  --fof                                   false
% 11.55/1.99  --time_out_real                         305.
% 11.55/1.99  --time_out_virtual                      -1.
% 11.55/1.99  --symbol_type_check                     false
% 11.55/1.99  --clausify_out                          false
% 11.55/1.99  --sig_cnt_out                           false
% 11.55/1.99  --trig_cnt_out                          false
% 11.55/1.99  --trig_cnt_out_tolerance                1.
% 11.55/1.99  --trig_cnt_out_sk_spl                   false
% 11.55/1.99  --abstr_cl_out                          false
% 11.55/1.99  
% 11.55/1.99  ------ Global Options
% 11.55/1.99  
% 11.55/1.99  --schedule                              default
% 11.55/1.99  --add_important_lit                     false
% 11.55/1.99  --prop_solver_per_cl                    1000
% 11.55/1.99  --min_unsat_core                        false
% 11.55/1.99  --soft_assumptions                      false
% 11.55/1.99  --soft_lemma_size                       3
% 11.55/1.99  --prop_impl_unit_size                   0
% 11.55/1.99  --prop_impl_unit                        []
% 11.55/1.99  --share_sel_clauses                     true
% 11.55/1.99  --reset_solvers                         false
% 11.55/1.99  --bc_imp_inh                            [conj_cone]
% 11.55/1.99  --conj_cone_tolerance                   3.
% 11.55/1.99  --extra_neg_conj                        none
% 11.55/1.99  --large_theory_mode                     true
% 11.55/1.99  --prolific_symb_bound                   200
% 11.55/1.99  --lt_threshold                          2000
% 11.55/1.99  --clause_weak_htbl                      true
% 11.55/1.99  --gc_record_bc_elim                     false
% 11.55/1.99  
% 11.55/1.99  ------ Preprocessing Options
% 11.55/1.99  
% 11.55/1.99  --preprocessing_flag                    true
% 11.55/1.99  --time_out_prep_mult                    0.1
% 11.55/1.99  --splitting_mode                        input
% 11.55/1.99  --splitting_grd                         true
% 11.55/1.99  --splitting_cvd                         false
% 11.55/1.99  --splitting_cvd_svl                     false
% 11.55/1.99  --splitting_nvd                         32
% 11.55/1.99  --sub_typing                            true
% 11.55/1.99  --prep_gs_sim                           true
% 11.55/1.99  --prep_unflatten                        true
% 11.55/1.99  --prep_res_sim                          true
% 11.55/1.99  --prep_upred                            true
% 11.55/1.99  --prep_sem_filter                       exhaustive
% 11.55/1.99  --prep_sem_filter_out                   false
% 11.55/1.99  --pred_elim                             true
% 11.55/1.99  --res_sim_input                         true
% 11.55/1.99  --eq_ax_congr_red                       true
% 11.55/1.99  --pure_diseq_elim                       true
% 11.55/1.99  --brand_transform                       false
% 11.55/1.99  --non_eq_to_eq                          false
% 11.55/1.99  --prep_def_merge                        true
% 11.55/1.99  --prep_def_merge_prop_impl              false
% 11.55/1.99  --prep_def_merge_mbd                    true
% 11.55/1.99  --prep_def_merge_tr_red                 false
% 11.55/1.99  --prep_def_merge_tr_cl                  false
% 11.55/1.99  --smt_preprocessing                     true
% 11.55/1.99  --smt_ac_axioms                         fast
% 11.55/1.99  --preprocessed_out                      false
% 11.55/1.99  --preprocessed_stats                    false
% 11.55/1.99  
% 11.55/1.99  ------ Abstraction refinement Options
% 11.55/1.99  
% 11.55/1.99  --abstr_ref                             []
% 11.55/1.99  --abstr_ref_prep                        false
% 11.55/1.99  --abstr_ref_until_sat                   false
% 11.55/1.99  --abstr_ref_sig_restrict                funpre
% 11.55/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.55/1.99  --abstr_ref_under                       []
% 11.55/1.99  
% 11.55/1.99  ------ SAT Options
% 11.55/1.99  
% 11.55/1.99  --sat_mode                              false
% 11.55/1.99  --sat_fm_restart_options                ""
% 11.55/1.99  --sat_gr_def                            false
% 11.55/1.99  --sat_epr_types                         true
% 11.55/1.99  --sat_non_cyclic_types                  false
% 11.55/1.99  --sat_finite_models                     false
% 11.55/1.99  --sat_fm_lemmas                         false
% 11.55/1.99  --sat_fm_prep                           false
% 11.55/1.99  --sat_fm_uc_incr                        true
% 11.55/1.99  --sat_out_model                         small
% 11.55/1.99  --sat_out_clauses                       false
% 11.55/1.99  
% 11.55/1.99  ------ QBF Options
% 11.55/1.99  
% 11.55/1.99  --qbf_mode                              false
% 11.55/1.99  --qbf_elim_univ                         false
% 11.55/1.99  --qbf_dom_inst                          none
% 11.55/1.99  --qbf_dom_pre_inst                      false
% 11.55/1.99  --qbf_sk_in                             false
% 11.55/1.99  --qbf_pred_elim                         true
% 11.55/1.99  --qbf_split                             512
% 11.55/1.99  
% 11.55/1.99  ------ BMC1 Options
% 11.55/1.99  
% 11.55/1.99  --bmc1_incremental                      false
% 11.55/1.99  --bmc1_axioms                           reachable_all
% 11.55/1.99  --bmc1_min_bound                        0
% 11.55/1.99  --bmc1_max_bound                        -1
% 11.55/1.99  --bmc1_max_bound_default                -1
% 11.55/1.99  --bmc1_symbol_reachability              true
% 11.55/1.99  --bmc1_property_lemmas                  false
% 11.55/1.99  --bmc1_k_induction                      false
% 11.55/1.99  --bmc1_non_equiv_states                 false
% 11.55/1.99  --bmc1_deadlock                         false
% 11.55/1.99  --bmc1_ucm                              false
% 11.55/1.99  --bmc1_add_unsat_core                   none
% 11.55/1.99  --bmc1_unsat_core_children              false
% 11.55/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.55/1.99  --bmc1_out_stat                         full
% 11.55/1.99  --bmc1_ground_init                      false
% 11.55/1.99  --bmc1_pre_inst_next_state              false
% 11.55/1.99  --bmc1_pre_inst_state                   false
% 11.55/1.99  --bmc1_pre_inst_reach_state             false
% 11.55/1.99  --bmc1_out_unsat_core                   false
% 11.55/1.99  --bmc1_aig_witness_out                  false
% 11.55/1.99  --bmc1_verbose                          false
% 11.55/1.99  --bmc1_dump_clauses_tptp                false
% 11.55/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.55/1.99  --bmc1_dump_file                        -
% 11.55/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.55/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.55/1.99  --bmc1_ucm_extend_mode                  1
% 11.55/1.99  --bmc1_ucm_init_mode                    2
% 11.55/1.99  --bmc1_ucm_cone_mode                    none
% 11.55/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.55/1.99  --bmc1_ucm_relax_model                  4
% 11.55/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.55/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.55/1.99  --bmc1_ucm_layered_model                none
% 11.55/1.99  --bmc1_ucm_max_lemma_size               10
% 11.55/1.99  
% 11.55/1.99  ------ AIG Options
% 11.55/1.99  
% 11.55/1.99  --aig_mode                              false
% 11.55/1.99  
% 11.55/1.99  ------ Instantiation Options
% 11.55/1.99  
% 11.55/1.99  --instantiation_flag                    true
% 11.55/1.99  --inst_sos_flag                         true
% 11.55/1.99  --inst_sos_phase                        true
% 11.55/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.55/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.55/1.99  --inst_lit_sel_side                     none
% 11.55/1.99  --inst_solver_per_active                1400
% 11.55/1.99  --inst_solver_calls_frac                1.
% 11.55/1.99  --inst_passive_queue_type               priority_queues
% 11.55/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.55/1.99  --inst_passive_queues_freq              [25;2]
% 11.55/1.99  --inst_dismatching                      true
% 11.55/1.99  --inst_eager_unprocessed_to_passive     true
% 11.55/1.99  --inst_prop_sim_given                   true
% 11.55/1.99  --inst_prop_sim_new                     false
% 11.55/1.99  --inst_subs_new                         false
% 11.55/1.99  --inst_eq_res_simp                      false
% 11.55/1.99  --inst_subs_given                       false
% 11.55/1.99  --inst_orphan_elimination               true
% 11.55/1.99  --inst_learning_loop_flag               true
% 11.55/1.99  --inst_learning_start                   3000
% 11.55/1.99  --inst_learning_factor                  2
% 11.55/1.99  --inst_start_prop_sim_after_learn       3
% 11.55/1.99  --inst_sel_renew                        solver
% 11.55/1.99  --inst_lit_activity_flag                true
% 11.55/1.99  --inst_restr_to_given                   false
% 11.55/1.99  --inst_activity_threshold               500
% 11.55/1.99  --inst_out_proof                        true
% 11.55/1.99  
% 11.55/1.99  ------ Resolution Options
% 11.55/1.99  
% 11.55/1.99  --resolution_flag                       false
% 11.55/1.99  --res_lit_sel                           adaptive
% 11.55/1.99  --res_lit_sel_side                      none
% 11.55/1.99  --res_ordering                          kbo
% 11.55/1.99  --res_to_prop_solver                    active
% 11.55/1.99  --res_prop_simpl_new                    false
% 11.55/1.99  --res_prop_simpl_given                  true
% 11.55/1.99  --res_passive_queue_type                priority_queues
% 11.55/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.55/1.99  --res_passive_queues_freq               [15;5]
% 11.55/1.99  --res_forward_subs                      full
% 11.55/1.99  --res_backward_subs                     full
% 11.55/1.99  --res_forward_subs_resolution           true
% 11.55/1.99  --res_backward_subs_resolution          true
% 11.55/1.99  --res_orphan_elimination                true
% 11.55/1.99  --res_time_limit                        2.
% 11.55/1.99  --res_out_proof                         true
% 11.55/1.99  
% 11.55/1.99  ------ Superposition Options
% 11.55/1.99  
% 11.55/1.99  --superposition_flag                    true
% 11.55/1.99  --sup_passive_queue_type                priority_queues
% 11.55/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.55/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.55/1.99  --demod_completeness_check              fast
% 11.55/1.99  --demod_use_ground                      true
% 11.55/1.99  --sup_to_prop_solver                    passive
% 11.55/1.99  --sup_prop_simpl_new                    true
% 11.55/1.99  --sup_prop_simpl_given                  true
% 11.55/1.99  --sup_fun_splitting                     true
% 11.55/1.99  --sup_smt_interval                      50000
% 11.55/1.99  
% 11.55/1.99  ------ Superposition Simplification Setup
% 11.55/1.99  
% 11.55/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.55/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.55/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.55/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.55/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.55/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.55/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.55/1.99  --sup_immed_triv                        [TrivRules]
% 11.55/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/1.99  --sup_immed_bw_main                     []
% 11.55/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.55/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.55/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/1.99  --sup_input_bw                          []
% 11.55/1.99  
% 11.55/1.99  ------ Combination Options
% 11.55/1.99  
% 11.55/1.99  --comb_res_mult                         3
% 11.55/1.99  --comb_sup_mult                         2
% 11.55/1.99  --comb_inst_mult                        10
% 11.55/1.99  
% 11.55/1.99  ------ Debug Options
% 11.55/1.99  
% 11.55/1.99  --dbg_backtrace                         false
% 11.55/1.99  --dbg_dump_prop_clauses                 false
% 11.55/1.99  --dbg_dump_prop_clauses_file            -
% 11.55/1.99  --dbg_out_stat                          false
% 11.55/1.99  
% 11.55/1.99  
% 11.55/1.99  
% 11.55/1.99  
% 11.55/1.99  ------ Proving...
% 11.55/1.99  
% 11.55/1.99  
% 11.55/1.99  % SZS status Theorem for theBenchmark.p
% 11.55/1.99  
% 11.55/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.55/1.99  
% 11.55/1.99  fof(f2,axiom,(
% 11.55/1.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f17,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.55/1.99    inference(ennf_transformation,[],[f2])).
% 11.55/1.99  
% 11.55/1.99  fof(f18,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.55/1.99    inference(flattening,[],[f17])).
% 11.55/1.99  
% 11.55/1.99  fof(f32,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.55/1.99    inference(cnf_transformation,[],[f18])).
% 11.55/1.99  
% 11.55/1.99  fof(f1,axiom,(
% 11.55/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f16,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.55/1.99    inference(ennf_transformation,[],[f1])).
% 11.55/1.99  
% 11.55/1.99  fof(f31,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.55/1.99    inference(cnf_transformation,[],[f16])).
% 11.55/1.99  
% 11.55/1.99  fof(f5,axiom,(
% 11.55/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f35,plain,(
% 11.55/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.55/1.99    inference(cnf_transformation,[],[f5])).
% 11.55/1.99  
% 11.55/1.99  fof(f47,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 11.55/1.99    inference(definition_unfolding,[],[f31,f35])).
% 11.55/1.99  
% 11.55/1.99  fof(f4,axiom,(
% 11.55/1.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f19,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.55/1.99    inference(ennf_transformation,[],[f4])).
% 11.55/1.99  
% 11.55/1.99  fof(f20,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.55/1.99    inference(flattening,[],[f19])).
% 11.55/1.99  
% 11.55/1.99  fof(f34,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.55/1.99    inference(cnf_transformation,[],[f20])).
% 11.55/1.99  
% 11.55/1.99  fof(f49,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.55/1.99    inference(definition_unfolding,[],[f34,f35])).
% 11.55/1.99  
% 11.55/1.99  fof(f9,axiom,(
% 11.55/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f40,plain,(
% 11.55/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.55/1.99    inference(cnf_transformation,[],[f9])).
% 11.55/1.99  
% 11.55/1.99  fof(f14,conjecture,(
% 11.55/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f15,negated_conjecture,(
% 11.55/1.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 11.55/1.99    inference(negated_conjecture,[],[f14])).
% 11.55/1.99  
% 11.55/1.99  fof(f27,plain,(
% 11.55/1.99    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.55/1.99    inference(ennf_transformation,[],[f15])).
% 11.55/1.99  
% 11.55/1.99  fof(f29,plain,(
% 11.55/1.99    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 11.55/1.99    introduced(choice_axiom,[])).
% 11.55/1.99  
% 11.55/1.99  fof(f30,plain,(
% 11.55/1.99    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.55/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29])).
% 11.55/1.99  
% 11.55/1.99  fof(f45,plain,(
% 11.55/1.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.55/1.99    inference(cnf_transformation,[],[f30])).
% 11.55/1.99  
% 11.55/1.99  fof(f6,axiom,(
% 11.55/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f28,plain,(
% 11.55/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.55/1.99    inference(nnf_transformation,[],[f6])).
% 11.55/1.99  
% 11.55/1.99  fof(f36,plain,(
% 11.55/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.55/1.99    inference(cnf_transformation,[],[f28])).
% 11.55/1.99  
% 11.55/1.99  fof(f7,axiom,(
% 11.55/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f21,plain,(
% 11.55/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.55/1.99    inference(ennf_transformation,[],[f7])).
% 11.55/1.99  
% 11.55/1.99  fof(f38,plain,(
% 11.55/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.55/1.99    inference(cnf_transformation,[],[f21])).
% 11.55/1.99  
% 11.55/1.99  fof(f37,plain,(
% 11.55/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.55/1.99    inference(cnf_transformation,[],[f28])).
% 11.55/1.99  
% 11.55/1.99  fof(f13,axiom,(
% 11.55/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f26,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.55/1.99    inference(ennf_transformation,[],[f13])).
% 11.55/1.99  
% 11.55/1.99  fof(f44,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.55/1.99    inference(cnf_transformation,[],[f26])).
% 11.55/1.99  
% 11.55/1.99  fof(f11,axiom,(
% 11.55/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f24,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.55/1.99    inference(ennf_transformation,[],[f11])).
% 11.55/1.99  
% 11.55/1.99  fof(f42,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.55/1.99    inference(cnf_transformation,[],[f24])).
% 11.55/1.99  
% 11.55/1.99  fof(f12,axiom,(
% 11.55/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f25,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.55/1.99    inference(ennf_transformation,[],[f12])).
% 11.55/1.99  
% 11.55/1.99  fof(f43,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.55/1.99    inference(cnf_transformation,[],[f25])).
% 11.55/1.99  
% 11.55/1.99  fof(f10,axiom,(
% 11.55/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f23,plain,(
% 11.55/1.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.55/1.99    inference(ennf_transformation,[],[f10])).
% 11.55/1.99  
% 11.55/1.99  fof(f41,plain,(
% 11.55/1.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.55/1.99    inference(cnf_transformation,[],[f23])).
% 11.55/1.99  
% 11.55/1.99  fof(f8,axiom,(
% 11.55/1.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f22,plain,(
% 11.55/1.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 11.55/1.99    inference(ennf_transformation,[],[f8])).
% 11.55/1.99  
% 11.55/1.99  fof(f39,plain,(
% 11.55/1.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.55/1.99    inference(cnf_transformation,[],[f22])).
% 11.55/1.99  
% 11.55/1.99  fof(f50,plain,(
% 11.55/1.99    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.55/1.99    inference(definition_unfolding,[],[f39,f35])).
% 11.55/1.99  
% 11.55/1.99  fof(f3,axiom,(
% 11.55/1.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.55/1.99  
% 11.55/1.99  fof(f33,plain,(
% 11.55/1.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.55/1.99    inference(cnf_transformation,[],[f3])).
% 11.55/1.99  
% 11.55/1.99  fof(f48,plain,(
% 11.55/1.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 11.55/1.99    inference(definition_unfolding,[],[f33,f35])).
% 11.55/1.99  
% 11.55/1.99  fof(f46,plain,(
% 11.55/1.99    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 11.55/1.99    inference(cnf_transformation,[],[f30])).
% 11.55/1.99  
% 11.55/1.99  fof(f51,plain,(
% 11.55/1.99    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 11.55/1.99    inference(definition_unfolding,[],[f46,f35])).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1,plain,
% 11.55/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.55/1.99      inference(cnf_transformation,[],[f32]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_216,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,X1_43)
% 11.55/1.99      | ~ r1_tarski(X1_43,X2_43)
% 11.55/1.99      | r1_tarski(X0_43,X2_43) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_1]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1103,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,X1_43)
% 11.55/1.99      | ~ r1_tarski(X1_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_216]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_43398,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | ~ r1_tarski(k1_relat_1(sK2),X0_43)
% 11.55/1.99      | r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_1103]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_43403,plain,
% 11.55/1.99      ( r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | ~ r1_tarski(k1_relat_1(sK2),sK0)
% 11.55/1.99      | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_43398]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_0,plain,
% 11.55/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 11.55/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_217,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,X1_43)
% 11.55/1.99      | r1_tarski(X0_43,k3_tarski(k2_tarski(X2_43,X1_43))) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_0]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1106,plain,
% 11.55/1.99      ( r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | ~ r1_tarski(X0_43,sK1) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_217]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_14885,plain,
% 11.55/1.99      ( r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_1106]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_3,plain,
% 11.55/1.99      ( ~ r1_tarski(X0,X1)
% 11.55/1.99      | ~ r1_tarski(X2,X1)
% 11.55/1.99      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 11.55/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_214,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,X1_43)
% 11.55/1.99      | ~ r1_tarski(X2_43,X1_43)
% 11.55/1.99      | r1_tarski(k3_tarski(k2_tarski(X0_43,X2_43)),X1_43) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_3]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1717,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | ~ r1_tarski(X1_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | r1_tarski(k3_tarski(k2_tarski(X0_43,X1_43)),k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_214]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_11276,plain,
% 11.55/1.99      ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_1717]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_225,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,X1_43)
% 11.55/1.99      | r1_tarski(X2_43,X3_43)
% 11.55/1.99      | X2_43 != X0_43
% 11.55/1.99      | X3_43 != X1_43 ),
% 11.55/1.99      theory(equality) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1457,plain,
% 11.55/1.99      ( r1_tarski(X0_43,X1_43)
% 11.55/1.99      | ~ r1_tarski(X2_43,k3_tarski(k2_tarski(X3_43,X4_43)))
% 11.55/1.99      | X0_43 != X2_43
% 11.55/1.99      | X1_43 != k3_tarski(k2_tarski(X3_43,X4_43)) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_225]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_2194,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43)))
% 11.55/1.99      | r1_tarski(X3_43,k3_tarski(k2_tarski(X1_43,X2_43)))
% 11.55/1.99      | X3_43 != X0_43
% 11.55/1.99      | k3_tarski(k2_tarski(X1_43,X2_43)) != k3_tarski(k2_tarski(X1_43,X2_43)) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_1457]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_4266,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | k3_relat_1(sK2) != X0_43
% 11.55/1.99      | k3_tarski(k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(sK0,sK1)) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_2194]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_11169,plain,
% 11.55/1.99      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1)))
% 11.55/1.99      | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
% 11.55/1.99      | k3_tarski(k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(sK0,sK1)) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_4266]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_8,plain,
% 11.55/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.55/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_210,plain,
% 11.55/1.99      ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_8]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_608,plain,
% 11.55/1.99      ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) = iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_14,negated_conjecture,
% 11.55/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.55/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_204,negated_conjecture,
% 11.55/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_14]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_614,plain,
% 11.55/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_204]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_5,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.55/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_212,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 11.55/1.99      | r1_tarski(X0_43,X1_43) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_5]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_606,plain,
% 11.55/1.99      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 11.55/1.99      | r1_tarski(X0_43,X1_43) = iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_940,plain,
% 11.55/1.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_614,c_606]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_6,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.55/1.99      | ~ v1_relat_1(X1)
% 11.55/1.99      | v1_relat_1(X0) ),
% 11.55/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_4,plain,
% 11.55/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.55/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_120,plain,
% 11.55/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.55/1.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_121,plain,
% 11.55/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.55/1.99      inference(renaming,[status(thm)],[c_120]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_146,plain,
% 11.55/1.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.55/1.99      inference(bin_hyper_res,[status(thm)],[c_6,c_121]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_203,plain,
% 11.55/1.99      ( ~ r1_tarski(X0_43,X1_43)
% 11.55/1.99      | ~ v1_relat_1(X1_43)
% 11.55/1.99      | v1_relat_1(X0_43) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_146]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_615,plain,
% 11.55/1.99      ( r1_tarski(X0_43,X1_43) != iProver_top
% 11.55/1.99      | v1_relat_1(X1_43) != iProver_top
% 11.55/1.99      | v1_relat_1(X0_43) = iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_2477,plain,
% 11.55/1.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.55/1.99      | v1_relat_1(sK2) = iProver_top ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_940,c_615]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_2951,plain,
% 11.55/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_608,c_2477]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_12,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.55/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_206,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.55/1.99      | k2_relset_1(X1_43,X2_43,X0_43) = k2_relat_1(X0_43) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_12]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_612,plain,
% 11.55/1.99      ( k2_relset_1(X0_43,X1_43,X2_43) = k2_relat_1(X2_43)
% 11.55/1.99      | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_206]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1214,plain,
% 11.55/1.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_614,c_612]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_10,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/1.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 11.55/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_208,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.55/1.99      | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_10]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_610,plain,
% 11.55/1.99      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
% 11.55/1.99      | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) = iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1779,plain,
% 11.55/1.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 11.55/1.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_1214,c_610]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_15,plain,
% 11.55/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1999,plain,
% 11.55/1.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 11.55/1.99      inference(global_propositional_subsumption,
% 11.55/1.99                [status(thm)],
% 11.55/1.99                [c_1779,c_15]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_2003,plain,
% 11.55/1.99      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_1999,c_606]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_2004,plain,
% 11.55/1.99      ( r1_tarski(k2_relat_1(sK2),sK1) ),
% 11.55/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2003]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_219,plain,( X0_43 = X0_43 ),theory(equality) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1604,plain,
% 11.55/1.99      ( k3_tarski(k2_tarski(sK0,sK1)) = k3_tarski(k2_tarski(sK0,sK1)) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_219]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_11,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/1.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.55/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_207,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.55/1.99      | k1_relset_1(X1_43,X2_43,X0_43) = k1_relat_1(X0_43) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_11]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_611,plain,
% 11.55/1.99      ( k1_relset_1(X0_43,X1_43,X2_43) = k1_relat_1(X2_43)
% 11.55/1.99      | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1208,plain,
% 11.55/1.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_614,c_611]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_9,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.55/1.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 11.55/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_209,plain,
% 11.55/1.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.55/1.99      | m1_subset_1(k1_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X1_43)) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_9]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_609,plain,
% 11.55/1.99      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
% 11.55/1.99      | m1_subset_1(k1_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X1_43)) = iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1438,plain,
% 11.55/1.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
% 11.55/1.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_1208,c_609]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1529,plain,
% 11.55/1.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 11.55/1.99      inference(global_propositional_subsumption,
% 11.55/1.99                [status(thm)],
% 11.55/1.99                [c_1438,c_15]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1533,plain,
% 11.55/1.99      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 11.55/1.99      inference(superposition,[status(thm)],[c_1529,c_606]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1534,plain,
% 11.55/1.99      ( r1_tarski(k1_relat_1(sK2),sK0) ),
% 11.55/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_1533]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_7,plain,
% 11.55/1.99      ( ~ v1_relat_1(X0)
% 11.55/1.99      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 11.55/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_211,plain,
% 11.55/1.99      ( ~ v1_relat_1(X0_43)
% 11.55/1.99      | k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_7]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1500,plain,
% 11.55/1.99      ( ~ v1_relat_1(sK2)
% 11.55/1.99      | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_211]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1501,plain,
% 11.55/1.99      ( k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2)
% 11.55/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.55/1.99      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_2,plain,
% 11.55/1.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 11.55/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_215,plain,
% 11.55/1.99      ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,X1_43))) ),
% 11.55/1.99      inference(subtyping,[status(esa)],[c_2]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1440,plain,
% 11.55/1.99      ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_215]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_222,plain,
% 11.55/1.99      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 11.55/1.99      theory(equality) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_709,plain,
% 11.55/1.99      ( X0_43 != X1_43
% 11.55/1.99      | k3_relat_1(sK2) != X1_43
% 11.55/1.99      | k3_relat_1(sK2) = X0_43 ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_222]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_820,plain,
% 11.55/1.99      ( X0_43 != k3_relat_1(sK2)
% 11.55/1.99      | k3_relat_1(sK2) = X0_43
% 11.55/1.99      | k3_relat_1(sK2) != k3_relat_1(sK2) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_709]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_1028,plain,
% 11.55/1.99      ( k3_relat_1(sK2) != k3_relat_1(sK2)
% 11.55/1.99      | k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
% 11.55/1.99      | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) != k3_relat_1(sK2) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_820]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_808,plain,
% 11.55/1.99      ( k3_relat_1(sK2) = k3_relat_1(sK2) ),
% 11.55/1.99      inference(instantiation,[status(thm)],[c_219]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(c_13,negated_conjecture,
% 11.55/1.99      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.55/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.55/1.99  
% 11.55/1.99  cnf(contradiction,plain,
% 11.55/1.99      ( $false ),
% 11.55/1.99      inference(minisat,
% 11.55/1.99                [status(thm)],
% 11.55/1.99                [c_43403,c_14885,c_11276,c_11169,c_2951,c_2004,c_1604,
% 11.55/1.99                 c_1534,c_1501,c_1440,c_1028,c_808,c_13]) ).
% 11.55/1.99  
% 11.55/1.99  
% 11.55/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.55/1.99  
% 11.55/1.99  ------                               Statistics
% 11.55/1.99  
% 11.55/1.99  ------ General
% 11.55/1.99  
% 11.55/1.99  abstr_ref_over_cycles:                  0
% 11.55/1.99  abstr_ref_under_cycles:                 0
% 11.55/1.99  gc_basic_clause_elim:                   0
% 11.55/1.99  forced_gc_time:                         0
% 11.55/1.99  parsing_time:                           0.006
% 11.55/1.99  unif_index_cands_time:                  0.
% 11.55/1.99  unif_index_add_time:                    0.
% 11.55/1.99  orderings_time:                         0.
% 11.55/1.99  out_proof_time:                         0.011
% 11.55/1.99  total_time:                             1.449
% 11.55/1.99  num_of_symbols:                         49
% 11.55/1.99  num_of_terms:                           50379
% 11.55/1.99  
% 11.55/1.99  ------ Preprocessing
% 11.55/1.99  
% 11.55/1.99  num_of_splits:                          0
% 11.55/1.99  num_of_split_atoms:                     0
% 11.55/1.99  num_of_reused_defs:                     0
% 11.55/1.99  num_eq_ax_congr_red:                    16
% 11.55/1.99  num_of_sem_filtered_clauses:            1
% 11.55/1.99  num_of_subtypes:                        3
% 11.55/1.99  monotx_restored_types:                  0
% 11.55/1.99  sat_num_of_epr_types:                   0
% 11.55/1.99  sat_num_of_non_cyclic_types:            0
% 11.55/1.99  sat_guarded_non_collapsed_types:        0
% 11.55/1.99  num_pure_diseq_elim:                    0
% 11.55/1.99  simp_replaced_by:                       0
% 11.55/1.99  res_preprocessed:                       70
% 11.55/1.99  prep_upred:                             0
% 11.55/1.99  prep_unflattend:                        0
% 11.55/1.99  smt_new_axioms:                         0
% 11.55/1.99  pred_elim_cands:                        3
% 11.55/1.99  pred_elim:                              0
% 11.55/1.99  pred_elim_cl:                           0
% 11.55/1.99  pred_elim_cycles:                       1
% 11.55/1.99  merged_defs:                            6
% 11.55/1.99  merged_defs_ncl:                        0
% 11.55/1.99  bin_hyper_res:                          7
% 11.55/1.99  prep_cycles:                            3
% 11.55/1.99  pred_elim_time:                         0.
% 11.55/1.99  splitting_time:                         0.
% 11.55/1.99  sem_filter_time:                        0.
% 11.55/1.99  monotx_time:                            0.
% 11.55/1.99  subtype_inf_time:                       0.
% 11.55/1.99  
% 11.55/1.99  ------ Problem properties
% 11.55/1.99  
% 11.55/1.99  clauses:                                15
% 11.55/1.99  conjectures:                            2
% 11.55/1.99  epr:                                    2
% 11.55/1.99  horn:                                   15
% 11.55/1.99  ground:                                 2
% 11.55/1.99  unary:                                  4
% 11.55/1.99  binary:                                 8
% 11.55/1.99  lits:                                   29
% 11.55/1.99  lits_eq:                                3
% 11.55/1.99  fd_pure:                                0
% 11.55/1.99  fd_pseudo:                              0
% 11.55/1.99  fd_cond:                                0
% 11.55/1.99  fd_pseudo_cond:                         0
% 11.55/1.99  ac_symbols:                             0
% 11.55/1.99  
% 11.55/1.99  ------ Propositional Solver
% 11.55/1.99  
% 11.55/1.99  prop_solver_calls:                      31
% 11.55/1.99  prop_fast_solver_calls:                 909
% 11.55/1.99  smt_solver_calls:                       0
% 11.55/1.99  smt_fast_solver_calls:                  0
% 11.55/1.99  prop_num_of_clauses:                    18072
% 11.55/1.99  prop_preprocess_simplified:             23289
% 11.55/1.99  prop_fo_subsumed:                       13
% 11.55/1.99  prop_solver_time:                       0.
% 11.55/1.99  smt_solver_time:                        0.
% 11.55/1.99  smt_fast_solver_time:                   0.
% 11.55/1.99  prop_fast_solver_time:                  0.
% 11.55/1.99  prop_unsat_core_time:                   0.002
% 11.55/1.99  
% 11.55/1.99  ------ QBF
% 11.55/1.99  
% 11.55/1.99  qbf_q_res:                              0
% 11.55/1.99  qbf_num_tautologies:                    0
% 11.55/1.99  qbf_prep_cycles:                        0
% 11.55/1.99  
% 11.55/1.99  ------ BMC1
% 11.55/1.99  
% 11.55/1.99  bmc1_current_bound:                     -1
% 11.55/1.99  bmc1_last_solved_bound:                 -1
% 11.55/1.99  bmc1_unsat_core_size:                   -1
% 11.55/1.99  bmc1_unsat_core_parents_size:           -1
% 11.55/1.99  bmc1_merge_next_fun:                    0
% 11.55/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.55/1.99  
% 11.55/1.99  ------ Instantiation
% 11.55/1.99  
% 11.55/1.99  inst_num_of_clauses:                    3610
% 11.55/1.99  inst_num_in_passive:                    1142
% 11.55/1.99  inst_num_in_active:                     1188
% 11.55/1.99  inst_num_in_unprocessed:                1286
% 11.55/1.99  inst_num_of_loops:                      1258
% 11.55/1.99  inst_num_of_learning_restarts:          0
% 11.55/1.99  inst_num_moves_active_passive:          65
% 11.55/1.99  inst_lit_activity:                      0
% 11.55/1.99  inst_lit_activity_moves:                0
% 11.55/1.99  inst_num_tautologies:                   0
% 11.55/1.99  inst_num_prop_implied:                  0
% 11.55/1.99  inst_num_existing_simplified:           0
% 11.55/1.99  inst_num_eq_res_simplified:             0
% 11.55/1.99  inst_num_child_elim:                    0
% 11.55/1.99  inst_num_of_dismatching_blockings:      10199
% 11.55/1.99  inst_num_of_non_proper_insts:           7255
% 11.55/1.99  inst_num_of_duplicates:                 0
% 11.55/1.99  inst_inst_num_from_inst_to_res:         0
% 11.55/1.99  inst_dismatching_checking_time:         0.
% 11.55/1.99  
% 11.55/1.99  ------ Resolution
% 11.55/1.99  
% 11.55/1.99  res_num_of_clauses:                     0
% 11.55/1.99  res_num_in_passive:                     0
% 11.55/1.99  res_num_in_active:                      0
% 11.55/1.99  res_num_of_loops:                       73
% 11.55/1.99  res_forward_subset_subsumed:            786
% 11.55/1.99  res_backward_subset_subsumed:           20
% 11.55/1.99  res_forward_subsumed:                   0
% 11.55/1.99  res_backward_subsumed:                  0
% 11.55/1.99  res_forward_subsumption_resolution:     0
% 11.55/1.99  res_backward_subsumption_resolution:    0
% 11.55/1.99  res_clause_to_clause_subsumption:       16709
% 11.55/1.99  res_orphan_elimination:                 0
% 11.55/1.99  res_tautology_del:                      498
% 11.55/1.99  res_num_eq_res_simplified:              0
% 11.55/1.99  res_num_sel_changes:                    0
% 11.55/1.99  res_moves_from_active_to_pass:          0
% 11.55/1.99  
% 11.55/1.99  ------ Superposition
% 11.55/1.99  
% 11.55/1.99  sup_time_total:                         0.
% 11.55/1.99  sup_time_generating:                    0.
% 11.55/1.99  sup_time_sim_full:                      0.
% 11.55/1.99  sup_time_sim_immed:                     0.
% 11.55/1.99  
% 11.55/1.99  sup_num_of_clauses:                     1579
% 11.55/1.99  sup_num_in_active:                      241
% 11.55/1.99  sup_num_in_passive:                     1338
% 11.55/1.99  sup_num_of_loops:                       250
% 11.55/1.99  sup_fw_superposition:                   1148
% 11.55/1.99  sup_bw_superposition:                   1008
% 11.55/1.99  sup_immediate_simplified:               367
% 11.55/1.99  sup_given_eliminated:                   2
% 11.55/1.99  comparisons_done:                       0
% 11.55/1.99  comparisons_avoided:                    0
% 11.55/1.99  
% 11.55/1.99  ------ Simplifications
% 11.55/1.99  
% 11.55/1.99  
% 11.55/1.99  sim_fw_subset_subsumed:                 136
% 11.55/1.99  sim_bw_subset_subsumed:                 17
% 11.55/1.99  sim_fw_subsumed:                        198
% 11.55/1.99  sim_bw_subsumed:                        30
% 11.55/1.99  sim_fw_subsumption_res:                 0
% 11.55/1.99  sim_bw_subsumption_res:                 0
% 11.55/1.99  sim_tautology_del:                      2
% 11.55/1.99  sim_eq_tautology_del:                   0
% 11.55/1.99  sim_eq_res_simp:                        0
% 11.55/1.99  sim_fw_demodulated:                     4
% 11.55/1.99  sim_bw_demodulated:                     0
% 11.55/1.99  sim_light_normalised:                   19
% 11.55/1.99  sim_joinable_taut:                      0
% 11.55/1.99  sim_joinable_simp:                      0
% 11.55/1.99  sim_ac_normalised:                      0
% 11.55/1.99  sim_smt_subsumption:                    0
% 11.55/1.99  
%------------------------------------------------------------------------------
