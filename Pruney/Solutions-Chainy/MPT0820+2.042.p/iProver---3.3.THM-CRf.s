%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:58 EST 2020

% Result     : Theorem 11.67s
% Output     : CNFRefutation 11.67s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 268 expanded)
%              Number of clauses        :   97 ( 141 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  344 ( 591 expanded)
%              Number of equality atoms :  108 ( 156 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f49,f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | k2_relset_1(X1_43,X2_43,X0_43) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_203,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_28014,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | X3_43 != k2_relat_1(X0_43)
    | k2_relset_1(X1_43,X2_43,X0_43) = X3_43 ),
    inference(resolution,[status(thm)],[c_186,c_203])).

cnf(c_200,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_26842,plain,
    ( X0_43 != X1_43
    | X1_43 = X0_43 ),
    inference(resolution,[status(thm)],[c_203,c_200])).

cnf(c_29868,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | X3_43 = k2_relset_1(X1_43,X2_43,X0_43)
    | X3_43 != k2_relat_1(X0_43) ),
    inference(resolution,[status(thm)],[c_28014,c_26842])).

cnf(c_206,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_28018,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | r1_tarski(X3_43,k2_relset_1(X1_43,X2_43,X0_43))
    | ~ r1_tarski(X4_43,k2_relat_1(X0_43))
    | X3_43 != X4_43 ),
    inference(resolution,[status(thm)],[c_186,c_206])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_184,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_31417,plain,
    ( r1_tarski(X0_43,k2_relset_1(sK0,sK1,sK2))
    | ~ r1_tarski(X1_43,k2_relat_1(sK2))
    | X0_43 != X1_43 ),
    inference(resolution,[status(thm)],[c_28018,c_184])).

cnf(c_39205,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | r1_tarski(X3_43,k2_relset_1(sK0,sK1,sK2))
    | ~ r1_tarski(k2_relset_1(X1_43,X2_43,X0_43),k2_relat_1(sK2))
    | X3_43 != k2_relat_1(X0_43) ),
    inference(resolution,[status(thm)],[c_29868,c_31417])).

cnf(c_26853,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X2_43,X1_43)
    | X2_43 != X0_43 ),
    inference(resolution,[status(thm)],[c_206,c_200])).

cnf(c_28016,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | r1_tarski(k2_relset_1(X1_43,X2_43,X0_43),X3_43)
    | ~ r1_tarski(k2_relat_1(X0_43),X3_43) ),
    inference(resolution,[status(thm)],[c_186,c_26853])).

cnf(c_29856,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK2),X0_43)
    | ~ r1_tarski(k2_relat_1(sK2),X0_43) ),
    inference(resolution,[status(thm)],[c_28016,c_184])).

cnf(c_39889,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(X0_43,k2_relset_1(sK0,sK1,sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | X0_43 != k2_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_39205,c_29856])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_198,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X0_43,k3_tarski(k2_tarski(X2_43,X1_43))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4775,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(X0_43,sK1) ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_4776,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1))) = iProver_top
    | r1_tarski(X0_43,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4775])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_196,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,X1_43))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_9492,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,sK1))) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_9493,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9492])).

cnf(c_9495,plain,
    ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9493])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_188,plain,
    ( v4_relat_1(X0_43,X1_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_12705,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_12706,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12705])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_191,plain,
    ( ~ v4_relat_1(X0_43,X1_43)
    | r1_tarski(k1_relat_1(X0_43),X1_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_12750,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_12751,plain,
    ( v4_relat_1(sK2,sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12750])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_111,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_112,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_139,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_112])).

cnf(c_183,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ v1_relat_1(X1_43)
    | v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_139])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_12728,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_193,c_184])).

cnf(c_12797,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_183,c_12728])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_189,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_12804,plain,
    ( v1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12797,c_189])).

cnf(c_12805,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12804])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_190,plain,
    ( ~ v1_relat_1(X0_43)
    | k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_12939,plain,
    ( ~ v1_relat_1(sK2)
    | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_12757,plain,
    ( X0_43 != X1_43
    | X0_43 = k3_tarski(k2_tarski(X2_43,X3_43))
    | k3_tarski(k2_tarski(X2_43,X3_43)) != X1_43 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_12897,plain,
    ( X0_43 != k3_relat_1(X1_43)
    | X0_43 = k3_tarski(k2_tarski(k1_relat_1(X1_43),k2_relat_1(X1_43)))
    | k3_tarski(k2_tarski(k1_relat_1(X1_43),k2_relat_1(X1_43))) != k3_relat_1(X1_43) ),
    inference(instantiation,[status(thm)],[c_12757])).

cnf(c_12928,plain,
    ( k3_relat_1(X0_43) != k3_relat_1(X0_43)
    | k3_relat_1(X0_43) = k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43)))
    | k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43))) != k3_relat_1(X0_43) ),
    inference(instantiation,[status(thm)],[c_12897])).

cnf(c_12929,plain,
    ( k3_relat_1(X0_43) = k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43)))
    | k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43))) != k3_relat_1(X0_43) ),
    inference(equality_resolution_simp,[status(thm)],[c_12928])).

cnf(c_12944,plain,
    ( k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
    | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) != k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12929])).

cnf(c_12847,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,k3_tarski(k2_tarski(X3_43,X4_43)))
    | X0_43 != X2_43
    | X1_43 != k3_tarski(k2_tarski(X3_43,X4_43)) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_13202,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43)))
    | r1_tarski(X3_43,k3_tarski(k2_tarski(X1_43,X2_43)))
    | X3_43 != X0_43
    | k3_tarski(k2_tarski(X1_43,X2_43)) != k3_tarski(k2_tarski(X1_43,X2_43)) ),
    inference(instantiation,[status(thm)],[c_12847])).

cnf(c_13203,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43)))
    | r1_tarski(X3_43,k3_tarski(k2_tarski(X1_43,X2_43)))
    | X3_43 != X0_43 ),
    inference(equality_resolution_simp,[status(thm)],[c_13202])).

cnf(c_13218,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
    | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | k3_relat_1(sK2) != X0_43 ),
    inference(instantiation,[status(thm)],[c_13203])).

cnf(c_13236,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1)))
    | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_13218])).

cnf(c_13237,plain,
    ( k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
    | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13236])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X1_43)
    | r1_tarski(k3_tarski(k2_tarski(X0_43,X2_43)),X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_12852,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43)))
    | ~ r1_tarski(X3_43,k3_tarski(k2_tarski(X1_43,X2_43)))
    | r1_tarski(k3_tarski(k2_tarski(X0_43,X3_43)),k3_tarski(k2_tarski(X1_43,X2_43))) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_13497,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_12852])).

cnf(c_13498,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13497])).

cnf(c_12602,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_12600,plain,
    ( k2_relset_1(X0_43,X1_43,X2_43) = k2_relat_1(X2_43)
    | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_13143,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_12602,c_12600])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_12599,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_13600,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13143,c_12599])).

cnf(c_13801,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13600,c_16])).

cnf(c_12594,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_13806,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_13801,c_12594])).

cnf(c_18120,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | k2_relat_1(sK2) != X0_43 ),
    inference(instantiation,[status(thm)],[c_13203])).

cnf(c_18121,plain,
    ( k2_relat_1(sK2) != X0_43
    | r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18120])).

cnf(c_14745,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | X0_43 != k2_relat_1(sK2)
    | X1_43 != sK1 ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_18229,plain,
    ( r1_tarski(X0_43,sK1)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | X0_43 != k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_14745])).

cnf(c_18230,plain,
    ( r1_tarski(X0_43,sK1)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | X0_43 != k2_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_18229])).

cnf(c_18231,plain,
    ( X0_43 != k2_relat_1(sK2)
    | r1_tarski(X0_43,sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18230])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_197,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X1_43,X2_43)
    | r1_tarski(X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_26299,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X1_43,k3_tarski(k2_tarski(X2_43,X3_43)))
    | r1_tarski(X0_43,k3_tarski(k2_tarski(X2_43,X3_43))) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_31320,plain,
    ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),X0_43)
    | r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_26299])).

cnf(c_31321,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_43) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31320])).

cnf(c_31323,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
    | r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31321])).

cnf(c_28848,plain,
    ( X0_43 != X1_43
    | k2_relat_1(sK2) != X1_43
    | k2_relat_1(sK2) = X0_43 ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_39559,plain,
    ( X0_43 != k2_relat_1(sK2)
    | k2_relat_1(sK2) = X0_43
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_28848])).

cnf(c_39560,plain,
    ( X0_43 != k2_relat_1(sK2)
    | k2_relat_1(sK2) = X0_43 ),
    inference(equality_resolution_simp,[status(thm)],[c_39559])).

cnf(c_39892,plain,
    ( X0_43 != k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39889,c_16,c_17,c_4776,c_9495,c_12706,c_12751,c_12804,c_12805,c_12939,c_12944,c_13237,c_13498,c_13806,c_18121,c_18231,c_31323,c_39560])).

cnf(c_39903,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_39892,c_200])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.67/2.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/2.02  
% 11.67/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.67/2.02  
% 11.67/2.02  ------  iProver source info
% 11.67/2.02  
% 11.67/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.67/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.67/2.02  git: non_committed_changes: false
% 11.67/2.02  git: last_make_outside_of_git: false
% 11.67/2.02  
% 11.67/2.02  ------ 
% 11.67/2.02  ------ Parsing...
% 11.67/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  ------ Proving...
% 11.67/2.02  ------ Problem Properties 
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  clauses                                 16
% 11.67/2.02  conjectures                             2
% 11.67/2.02  EPR                                     2
% 11.67/2.02  Horn                                    16
% 11.67/2.02  unary                                   4
% 11.67/2.02  binary                                  7
% 11.67/2.02  lits                                    33
% 11.67/2.02  lits eq                                 2
% 11.67/2.02  fd_pure                                 0
% 11.67/2.02  fd_pseudo                               0
% 11.67/2.02  fd_cond                                 0
% 11.67/2.02  fd_pseudo_cond                          0
% 11.67/2.02  AC symbols                              0
% 11.67/2.02  
% 11.67/2.02  ------ Input Options Time Limit: Unbounded
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing...
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.67/2.02  Current options:
% 11.67/2.02  ------ 
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.67/2.02  
% 11.67/2.02  ------ Proving...
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  % SZS status Theorem for theBenchmark.p
% 11.67/2.02  
% 11.67/2.02   Resolution empty clause
% 11.67/2.02  
% 11.67/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.67/2.02  
% 11.67/2.02  fof(f13,axiom,(
% 11.67/2.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f27,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.67/2.02    inference(ennf_transformation,[],[f13])).
% 11.67/2.02  
% 11.67/2.02  fof(f47,plain,(
% 11.67/2.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.67/2.02    inference(cnf_transformation,[],[f27])).
% 11.67/2.02  
% 11.67/2.02  fof(f14,conjecture,(
% 11.67/2.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f15,negated_conjecture,(
% 11.67/2.02    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 11.67/2.02    inference(negated_conjecture,[],[f14])).
% 11.67/2.02  
% 11.67/2.02  fof(f28,plain,(
% 11.67/2.02    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.67/2.02    inference(ennf_transformation,[],[f15])).
% 11.67/2.02  
% 11.67/2.02  fof(f31,plain,(
% 11.67/2.02    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 11.67/2.02    introduced(choice_axiom,[])).
% 11.67/2.02  
% 11.67/2.02  fof(f32,plain,(
% 11.67/2.02    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.67/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).
% 11.67/2.02  
% 11.67/2.02  fof(f48,plain,(
% 11.67/2.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.67/2.02    inference(cnf_transformation,[],[f32])).
% 11.67/2.02  
% 11.67/2.02  fof(f49,plain,(
% 11.67/2.02    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 11.67/2.02    inference(cnf_transformation,[],[f32])).
% 11.67/2.02  
% 11.67/2.02  fof(f5,axiom,(
% 11.67/2.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f37,plain,(
% 11.67/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.67/2.02    inference(cnf_transformation,[],[f5])).
% 11.67/2.02  
% 11.67/2.02  fof(f54,plain,(
% 11.67/2.02    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 11.67/2.02    inference(definition_unfolding,[],[f49,f37])).
% 11.67/2.02  
% 11.67/2.02  fof(f1,axiom,(
% 11.67/2.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f17,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.67/2.02    inference(ennf_transformation,[],[f1])).
% 11.67/2.02  
% 11.67/2.02  fof(f33,plain,(
% 11.67/2.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.67/2.02    inference(cnf_transformation,[],[f17])).
% 11.67/2.02  
% 11.67/2.02  fof(f50,plain,(
% 11.67/2.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 11.67/2.02    inference(definition_unfolding,[],[f33,f37])).
% 11.67/2.02  
% 11.67/2.02  fof(f3,axiom,(
% 11.67/2.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f35,plain,(
% 11.67/2.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.67/2.02    inference(cnf_transformation,[],[f3])).
% 11.67/2.02  
% 11.67/2.02  fof(f51,plain,(
% 11.67/2.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 11.67/2.02    inference(definition_unfolding,[],[f35,f37])).
% 11.67/2.02  
% 11.67/2.02  fof(f11,axiom,(
% 11.67/2.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f16,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.67/2.02    inference(pure_predicate_removal,[],[f11])).
% 11.67/2.02  
% 11.67/2.02  fof(f25,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.67/2.02    inference(ennf_transformation,[],[f16])).
% 11.67/2.02  
% 11.67/2.02  fof(f45,plain,(
% 11.67/2.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.67/2.02    inference(cnf_transformation,[],[f25])).
% 11.67/2.02  
% 11.67/2.02  fof(f8,axiom,(
% 11.67/2.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f23,plain,(
% 11.67/2.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.67/2.02    inference(ennf_transformation,[],[f8])).
% 11.67/2.02  
% 11.67/2.02  fof(f30,plain,(
% 11.67/2.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.67/2.02    inference(nnf_transformation,[],[f23])).
% 11.67/2.02  
% 11.67/2.02  fof(f41,plain,(
% 11.67/2.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.67/2.02    inference(cnf_transformation,[],[f30])).
% 11.67/2.02  
% 11.67/2.02  fof(f7,axiom,(
% 11.67/2.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f22,plain,(
% 11.67/2.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.67/2.02    inference(ennf_transformation,[],[f7])).
% 11.67/2.02  
% 11.67/2.02  fof(f40,plain,(
% 11.67/2.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.67/2.02    inference(cnf_transformation,[],[f22])).
% 11.67/2.02  
% 11.67/2.02  fof(f6,axiom,(
% 11.67/2.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f29,plain,(
% 11.67/2.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.67/2.02    inference(nnf_transformation,[],[f6])).
% 11.67/2.02  
% 11.67/2.02  fof(f39,plain,(
% 11.67/2.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.67/2.02    inference(cnf_transformation,[],[f29])).
% 11.67/2.02  
% 11.67/2.02  fof(f38,plain,(
% 11.67/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.67/2.02    inference(cnf_transformation,[],[f29])).
% 11.67/2.02  
% 11.67/2.02  fof(f10,axiom,(
% 11.67/2.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f44,plain,(
% 11.67/2.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.67/2.02    inference(cnf_transformation,[],[f10])).
% 11.67/2.02  
% 11.67/2.02  fof(f9,axiom,(
% 11.67/2.02    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f24,plain,(
% 11.67/2.02    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 11.67/2.02    inference(ennf_transformation,[],[f9])).
% 11.67/2.02  
% 11.67/2.02  fof(f43,plain,(
% 11.67/2.02    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.67/2.02    inference(cnf_transformation,[],[f24])).
% 11.67/2.02  
% 11.67/2.02  fof(f53,plain,(
% 11.67/2.02    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.67/2.02    inference(definition_unfolding,[],[f43,f37])).
% 11.67/2.02  
% 11.67/2.02  fof(f4,axiom,(
% 11.67/2.02    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f20,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.67/2.02    inference(ennf_transformation,[],[f4])).
% 11.67/2.02  
% 11.67/2.02  fof(f21,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.67/2.02    inference(flattening,[],[f20])).
% 11.67/2.02  
% 11.67/2.02  fof(f36,plain,(
% 11.67/2.02    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.67/2.02    inference(cnf_transformation,[],[f21])).
% 11.67/2.02  
% 11.67/2.02  fof(f52,plain,(
% 11.67/2.02    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.67/2.02    inference(definition_unfolding,[],[f36,f37])).
% 11.67/2.02  
% 11.67/2.02  fof(f12,axiom,(
% 11.67/2.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f26,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.67/2.02    inference(ennf_transformation,[],[f12])).
% 11.67/2.02  
% 11.67/2.02  fof(f46,plain,(
% 11.67/2.02    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.67/2.02    inference(cnf_transformation,[],[f26])).
% 11.67/2.02  
% 11.67/2.02  fof(f2,axiom,(
% 11.67/2.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.67/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/2.02  
% 11.67/2.02  fof(f18,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.67/2.02    inference(ennf_transformation,[],[f2])).
% 11.67/2.02  
% 11.67/2.02  fof(f19,plain,(
% 11.67/2.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.67/2.02    inference(flattening,[],[f18])).
% 11.67/2.02  
% 11.67/2.02  fof(f34,plain,(
% 11.67/2.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.67/2.02    inference(cnf_transformation,[],[f19])).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.67/2.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.67/2.02      inference(cnf_transformation,[],[f47]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_186,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.67/2.02      | k2_relset_1(X1_43,X2_43,X0_43) = k2_relat_1(X0_43) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_13]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_203,plain,
% 11.67/2.02      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 11.67/2.02      theory(equality) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_28014,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.67/2.02      | X3_43 != k2_relat_1(X0_43)
% 11.67/2.02      | k2_relset_1(X1_43,X2_43,X0_43) = X3_43 ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_186,c_203]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_200,plain,( X0_43 = X0_43 ),theory(equality) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_26842,plain,
% 11.67/2.02      ( X0_43 != X1_43 | X1_43 = X0_43 ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_203,c_200]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_29868,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.67/2.02      | X3_43 = k2_relset_1(X1_43,X2_43,X0_43)
% 11.67/2.02      | X3_43 != k2_relat_1(X0_43) ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_28014,c_26842]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_206,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,X1_43)
% 11.67/2.02      | r1_tarski(X2_43,X3_43)
% 11.67/2.02      | X2_43 != X0_43
% 11.67/2.02      | X3_43 != X1_43 ),
% 11.67/2.02      theory(equality) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_28018,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.67/2.02      | r1_tarski(X3_43,k2_relset_1(X1_43,X2_43,X0_43))
% 11.67/2.02      | ~ r1_tarski(X4_43,k2_relat_1(X0_43))
% 11.67/2.02      | X3_43 != X4_43 ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_186,c_206]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_15,negated_conjecture,
% 11.67/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.67/2.02      inference(cnf_transformation,[],[f48]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_184,negated_conjecture,
% 11.67/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_15]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_31417,plain,
% 11.67/2.02      ( r1_tarski(X0_43,k2_relset_1(sK0,sK1,sK2))
% 11.67/2.02      | ~ r1_tarski(X1_43,k2_relat_1(sK2))
% 11.67/2.02      | X0_43 != X1_43 ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_28018,c_184]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_39205,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.67/2.02      | r1_tarski(X3_43,k2_relset_1(sK0,sK1,sK2))
% 11.67/2.02      | ~ r1_tarski(k2_relset_1(X1_43,X2_43,X0_43),k2_relat_1(sK2))
% 11.67/2.02      | X3_43 != k2_relat_1(X0_43) ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_29868,c_31417]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_26853,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,X1_43) | r1_tarski(X2_43,X1_43) | X2_43 != X0_43 ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_206,c_200]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_28016,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.67/2.02      | r1_tarski(k2_relset_1(X1_43,X2_43,X0_43),X3_43)
% 11.67/2.02      | ~ r1_tarski(k2_relat_1(X0_43),X3_43) ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_186,c_26853]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_29856,plain,
% 11.67/2.02      ( r1_tarski(k2_relset_1(sK0,sK1,sK2),X0_43)
% 11.67/2.02      | ~ r1_tarski(k2_relat_1(sK2),X0_43) ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_28016,c_184]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_39889,plain,
% 11.67/2.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.67/2.02      | r1_tarski(X0_43,k2_relset_1(sK0,sK1,sK2))
% 11.67/2.02      | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
% 11.67/2.02      | X0_43 != k2_relat_1(sK2) ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_39205,c_29856]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_16,plain,
% 11.67/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_14,negated_conjecture,
% 11.67/2.02      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.67/2.02      inference(cnf_transformation,[],[f54]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_17,plain,
% 11.67/2.02      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_0,plain,
% 11.67/2.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 11.67/2.02      inference(cnf_transformation,[],[f50]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_198,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,X1_43)
% 11.67/2.02      | r1_tarski(X0_43,k3_tarski(k2_tarski(X2_43,X1_43))) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_0]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_4775,plain,
% 11.67/2.02      ( r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | ~ r1_tarski(X0_43,sK1) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_198]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_4776,plain,
% 11.67/2.02      ( r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1))) = iProver_top
% 11.67/2.02      | r1_tarski(X0_43,sK1) != iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_4775]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_2,plain,
% 11.67/2.02      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 11.67/2.02      inference(cnf_transformation,[],[f51]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_196,plain,
% 11.67/2.02      ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,X1_43))) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_2]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_9492,plain,
% 11.67/2.02      ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,sK1))) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_196]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_9493,plain,
% 11.67/2.02      ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,sK1))) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_9492]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_9495,plain,
% 11.67/2.02      ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_9493]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_11,plain,
% 11.67/2.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.67/2.02      inference(cnf_transformation,[],[f45]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_188,plain,
% 11.67/2.02      ( v4_relat_1(X0_43,X1_43)
% 11.67/2.02      | ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_11]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12705,plain,
% 11.67/2.02      ( v4_relat_1(sK2,sK0)
% 11.67/2.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_188]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12706,plain,
% 11.67/2.02      ( v4_relat_1(sK2,sK0) = iProver_top
% 11.67/2.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_12705]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_8,plain,
% 11.67/2.02      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 11.67/2.02      inference(cnf_transformation,[],[f41]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_191,plain,
% 11.67/2.02      ( ~ v4_relat_1(X0_43,X1_43)
% 11.67/2.02      | r1_tarski(k1_relat_1(X0_43),X1_43)
% 11.67/2.02      | ~ v1_relat_1(X0_43) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_8]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12750,plain,
% 11.67/2.02      ( ~ v4_relat_1(sK2,sK0)
% 11.67/2.02      | r1_tarski(k1_relat_1(sK2),sK0)
% 11.67/2.02      | ~ v1_relat_1(sK2) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_191]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12751,plain,
% 11.67/2.02      ( v4_relat_1(sK2,sK0) != iProver_top
% 11.67/2.02      | r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 11.67/2.02      | v1_relat_1(sK2) != iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_12750]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_6,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.67/2.02      inference(cnf_transformation,[],[f40]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_4,plain,
% 11.67/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.67/2.02      inference(cnf_transformation,[],[f39]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_111,plain,
% 11.67/2.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.67/2.02      inference(prop_impl,[status(thm)],[c_4]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_112,plain,
% 11.67/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.67/2.02      inference(renaming,[status(thm)],[c_111]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_139,plain,
% 11.67/2.02      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.67/2.02      inference(bin_hyper_res,[status(thm)],[c_6,c_112]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_183,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,X1_43) | ~ v1_relat_1(X1_43) | v1_relat_1(X0_43) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_139]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_5,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.67/2.02      inference(cnf_transformation,[],[f38]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_193,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) | r1_tarski(X0_43,X1_43) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_5]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12728,plain,
% 11.67/2.02      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_193,c_184]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12797,plain,
% 11.67/2.02      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_183,c_12728]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_10,plain,
% 11.67/2.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.67/2.02      inference(cnf_transformation,[],[f44]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_189,plain,
% 11.67/2.02      ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_10]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12804,plain,
% 11.67/2.02      ( v1_relat_1(sK2) ),
% 11.67/2.02      inference(forward_subsumption_resolution,[status(thm)],[c_12797,c_189]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12805,plain,
% 11.67/2.02      ( v1_relat_1(sK2) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_12804]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_9,plain,
% 11.67/2.02      ( ~ v1_relat_1(X0)
% 11.67/2.02      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 11.67/2.02      inference(cnf_transformation,[],[f53]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_190,plain,
% 11.67/2.02      ( ~ v1_relat_1(X0_43)
% 11.67/2.02      | k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_9]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12939,plain,
% 11.67/2.02      ( ~ v1_relat_1(sK2)
% 11.67/2.02      | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_190]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12757,plain,
% 11.67/2.02      ( X0_43 != X1_43
% 11.67/2.02      | X0_43 = k3_tarski(k2_tarski(X2_43,X3_43))
% 11.67/2.02      | k3_tarski(k2_tarski(X2_43,X3_43)) != X1_43 ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_203]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12897,plain,
% 11.67/2.02      ( X0_43 != k3_relat_1(X1_43)
% 11.67/2.02      | X0_43 = k3_tarski(k2_tarski(k1_relat_1(X1_43),k2_relat_1(X1_43)))
% 11.67/2.02      | k3_tarski(k2_tarski(k1_relat_1(X1_43),k2_relat_1(X1_43))) != k3_relat_1(X1_43) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_12757]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12928,plain,
% 11.67/2.02      ( k3_relat_1(X0_43) != k3_relat_1(X0_43)
% 11.67/2.02      | k3_relat_1(X0_43) = k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43)))
% 11.67/2.02      | k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43))) != k3_relat_1(X0_43) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_12897]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12929,plain,
% 11.67/2.02      ( k3_relat_1(X0_43) = k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43)))
% 11.67/2.02      | k3_tarski(k2_tarski(k1_relat_1(X0_43),k2_relat_1(X0_43))) != k3_relat_1(X0_43) ),
% 11.67/2.02      inference(equality_resolution_simp,[status(thm)],[c_12928]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12944,plain,
% 11.67/2.02      ( k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
% 11.67/2.02      | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) != k3_relat_1(sK2) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_12929]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12847,plain,
% 11.67/2.02      ( r1_tarski(X0_43,X1_43)
% 11.67/2.02      | ~ r1_tarski(X2_43,k3_tarski(k2_tarski(X3_43,X4_43)))
% 11.67/2.02      | X0_43 != X2_43
% 11.67/2.02      | X1_43 != k3_tarski(k2_tarski(X3_43,X4_43)) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_206]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13202,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43)))
% 11.67/2.02      | r1_tarski(X3_43,k3_tarski(k2_tarski(X1_43,X2_43)))
% 11.67/2.02      | X3_43 != X0_43
% 11.67/2.02      | k3_tarski(k2_tarski(X1_43,X2_43)) != k3_tarski(k2_tarski(X1_43,X2_43)) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_12847]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13203,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43)))
% 11.67/2.02      | r1_tarski(X3_43,k3_tarski(k2_tarski(X1_43,X2_43)))
% 11.67/2.02      | X3_43 != X0_43 ),
% 11.67/2.02      inference(equality_resolution_simp,[status(thm)],[c_13202]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13218,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | k3_relat_1(sK2) != X0_43 ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_13203]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13236,plain,
% 11.67/2.02      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_13218]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13237,plain,
% 11.67/2.02      ( k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
% 11.67/2.02      | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top
% 11.67/2.02      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_13236]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_3,plain,
% 11.67/2.02      ( ~ r1_tarski(X0,X1)
% 11.67/2.02      | ~ r1_tarski(X2,X1)
% 11.67/2.02      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 11.67/2.02      inference(cnf_transformation,[],[f52]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_195,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,X1_43)
% 11.67/2.02      | ~ r1_tarski(X2_43,X1_43)
% 11.67/2.02      | r1_tarski(k3_tarski(k2_tarski(X0_43,X2_43)),X1_43) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_3]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12852,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43)))
% 11.67/2.02      | ~ r1_tarski(X3_43,k3_tarski(k2_tarski(X1_43,X2_43)))
% 11.67/2.02      | r1_tarski(k3_tarski(k2_tarski(X0_43,X3_43)),k3_tarski(k2_tarski(X1_43,X2_43))) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_195]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13497,plain,
% 11.67/2.02      ( ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_12852]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13498,plain,
% 11.67/2.02      ( r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top
% 11.67/2.02      | r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top
% 11.67/2.02      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_13497]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12602,plain,
% 11.67/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12600,plain,
% 11.67/2.02      ( k2_relset_1(X0_43,X1_43,X2_43) = k2_relat_1(X2_43)
% 11.67/2.02      | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13143,plain,
% 11.67/2.02      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.67/2.02      inference(superposition,[status(thm)],[c_12602,c_12600]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.67/2.02      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 11.67/2.02      inference(cnf_transformation,[],[f46]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_187,plain,
% 11.67/2.02      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 11.67/2.02      | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_12]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12599,plain,
% 11.67/2.02      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
% 11.67/2.02      | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13600,plain,
% 11.67/2.02      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 11.67/2.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 11.67/2.02      inference(superposition,[status(thm)],[c_13143,c_12599]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13801,plain,
% 11.67/2.02      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 11.67/2.02      inference(global_propositional_subsumption,[status(thm)],[c_13600,c_16]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_12594,plain,
% 11.67/2.02      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 11.67/2.02      | r1_tarski(X0_43,X1_43) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_13806,plain,
% 11.67/2.02      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 11.67/2.02      inference(superposition,[status(thm)],[c_13801,c_12594]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_18120,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | k2_relat_1(sK2) != X0_43 ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_13203]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_18121,plain,
% 11.67/2.02      ( k2_relat_1(sK2) != X0_43
% 11.67/2.02      | r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1))) != iProver_top
% 11.67/2.02      | r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_18120]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_14745,plain,
% 11.67/2.02      ( r1_tarski(X0_43,X1_43)
% 11.67/2.02      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 11.67/2.02      | X0_43 != k2_relat_1(sK2)
% 11.67/2.02      | X1_43 != sK1 ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_206]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_18229,plain,
% 11.67/2.02      ( r1_tarski(X0_43,sK1)
% 11.67/2.02      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 11.67/2.02      | X0_43 != k2_relat_1(sK2)
% 11.67/2.02      | sK1 != sK1 ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_14745]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_18230,plain,
% 11.67/2.02      ( r1_tarski(X0_43,sK1)
% 11.67/2.02      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 11.67/2.02      | X0_43 != k2_relat_1(sK2) ),
% 11.67/2.02      inference(equality_resolution_simp,[status(thm)],[c_18229]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_18231,plain,
% 11.67/2.02      ( X0_43 != k2_relat_1(sK2)
% 11.67/2.02      | r1_tarski(X0_43,sK1) = iProver_top
% 11.67/2.02      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_18230]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_1,plain,
% 11.67/2.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.67/2.02      inference(cnf_transformation,[],[f34]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_197,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,X1_43)
% 11.67/2.02      | ~ r1_tarski(X1_43,X2_43)
% 11.67/2.02      | r1_tarski(X0_43,X2_43) ),
% 11.67/2.02      inference(subtyping,[status(esa)],[c_1]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_26299,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,X1_43)
% 11.67/2.02      | ~ r1_tarski(X1_43,k3_tarski(k2_tarski(X2_43,X3_43)))
% 11.67/2.02      | r1_tarski(X0_43,k3_tarski(k2_tarski(X2_43,X3_43))) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_197]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_31320,plain,
% 11.67/2.02      ( ~ r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1)))
% 11.67/2.02      | ~ r1_tarski(k1_relat_1(sK2),X0_43)
% 11.67/2.02      | r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_26299]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_31321,plain,
% 11.67/2.02      ( r1_tarski(X0_43,k3_tarski(k2_tarski(sK0,sK1))) != iProver_top
% 11.67/2.02      | r1_tarski(k1_relat_1(sK2),X0_43) != iProver_top
% 11.67/2.02      | r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
% 11.67/2.02      inference(predicate_to_equality,[status(thm)],[c_31320]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_31323,plain,
% 11.67/2.02      ( r1_tarski(k1_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) = iProver_top
% 11.67/2.02      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
% 11.67/2.02      | r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_31321]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_28848,plain,
% 11.67/2.02      ( X0_43 != X1_43 | k2_relat_1(sK2) != X1_43 | k2_relat_1(sK2) = X0_43 ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_203]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_39559,plain,
% 11.67/2.02      ( X0_43 != k2_relat_1(sK2)
% 11.67/2.02      | k2_relat_1(sK2) = X0_43
% 11.67/2.02      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 11.67/2.02      inference(instantiation,[status(thm)],[c_28848]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_39560,plain,
% 11.67/2.02      ( X0_43 != k2_relat_1(sK2) | k2_relat_1(sK2) = X0_43 ),
% 11.67/2.02      inference(equality_resolution_simp,[status(thm)],[c_39559]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_39892,plain,
% 11.67/2.02      ( X0_43 != k2_relat_1(sK2) ),
% 11.67/2.02      inference(global_propositional_subsumption,
% 11.67/2.02                [status(thm)],
% 11.67/2.02                [c_39889,c_16,c_17,c_4776,c_9495,c_12706,c_12751,c_12804,
% 11.67/2.02                 c_12805,c_12939,c_12944,c_13237,c_13498,c_13806,c_18121,
% 11.67/2.02                 c_18231,c_31323,c_39560]) ).
% 11.67/2.02  
% 11.67/2.02  cnf(c_39903,plain,
% 11.67/2.02      ( $false ),
% 11.67/2.02      inference(resolution,[status(thm)],[c_39892,c_200]) ).
% 11.67/2.02  
% 11.67/2.02  
% 11.67/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.67/2.02  
% 11.67/2.02  ------                               Statistics
% 11.67/2.02  
% 11.67/2.02  ------ Selected
% 11.67/2.02  
% 11.67/2.02  total_time:                             1.2
% 11.67/2.02  
%------------------------------------------------------------------------------
