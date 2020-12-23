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
% DateTime   : Thu Dec  3 12:05:40 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 443 expanded)
%              Number of clauses        :   63 ( 134 expanded)
%              Number of leaves         :   17 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  308 (1312 expanded)
%              Number of equality atoms :  158 ( 542 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f35])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f57,f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f38,f37,f37])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f67,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f60])).

fof(f59,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ~ r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f59,f37,f37])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_tarski(k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_tarski(X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f37,f37])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1838,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_9])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_293,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_15])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_1836,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_2089,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_tarski(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1836])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k2_tarski(X2,X2) = X0
    | k2_tarski(X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1848,plain,
    ( k2_tarski(X0,X1) = X2
    | k2_tarski(X1,X1) = X2
    | k2_tarski(X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3248,plain,
    ( k2_tarski(sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2089,c_1848])).

cnf(c_1,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1851,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3354,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k2_tarski(X0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3248,c_1851])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1983,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2005,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
    | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2056,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
    | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_1409,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2010,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2) != X0
    | k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_2055,plain,
    ( r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_2170,plain,
    ( r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2055])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2171,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_tarski(X1,X1) != k1_relat_1(X0)
    | k2_tarski(k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_270,plain,
    ( ~ v1_relat_1(X0)
    | k2_tarski(X1,X1) != k1_relat_1(X0)
    | k2_tarski(k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_271,plain,
    ( ~ v1_relat_1(sK3)
    | k2_tarski(X0,X0) != k1_relat_1(sK3)
    | k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_1837,plain,
    ( k2_tarski(X0,X0) != k1_relat_1(sK3)
    | k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_272,plain,
    ( k2_tarski(X0,X0) != k1_relat_1(sK3)
    | k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_1984,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_1989,plain,
    ( k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_tarski(X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1837,c_23,c_272,c_1984])).

cnf(c_1990,plain,
    ( k2_tarski(X0,X0) != k1_relat_1(sK3)
    | k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1989])).

cnf(c_3356,plain,
    ( k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3248,c_1990])).

cnf(c_3417,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3354,c_20,c_18,c_1983,c_2056,c_2170,c_2171,c_3356])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1842,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3429,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_1842])).

cnf(c_1406,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2542,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_2769,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1407,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2543,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_3130,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2543])).

cnf(c_3131,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3130])).

cnf(c_3476,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3429,c_20,c_18,c_1983,c_2056,c_2170,c_2171,c_2542,c_2769,c_3131,c_3356])).

cnf(c_1840,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2691,plain,
    ( k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1838,c_1840])).

cnf(c_1839,plain,
    ( r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2890,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2691,c_1839])).

cnf(c_3480,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_tarski(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3476,c_2890])).

cnf(c_11,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3490,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3480,c_11])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1847,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1845,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2197,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1845])).

cnf(c_3577,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3490,c_2197])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.63/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/0.97  
% 2.63/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/0.97  
% 2.63/0.97  ------  iProver source info
% 2.63/0.97  
% 2.63/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.63/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/0.97  git: non_committed_changes: false
% 2.63/0.97  git: last_make_outside_of_git: false
% 2.63/0.97  
% 2.63/0.97  ------ 
% 2.63/0.97  
% 2.63/0.97  ------ Input Options
% 2.63/0.97  
% 2.63/0.97  --out_options                           all
% 2.63/0.97  --tptp_safe_out                         true
% 2.63/0.97  --problem_path                          ""
% 2.63/0.97  --include_path                          ""
% 2.63/0.97  --clausifier                            res/vclausify_rel
% 2.63/0.97  --clausifier_options                    --mode clausify
% 2.63/0.97  --stdin                                 false
% 2.63/0.97  --stats_out                             all
% 2.63/0.97  
% 2.63/0.97  ------ General Options
% 2.63/0.97  
% 2.63/0.97  --fof                                   false
% 2.63/0.97  --time_out_real                         305.
% 2.63/0.97  --time_out_virtual                      -1.
% 2.63/0.97  --symbol_type_check                     false
% 2.63/0.97  --clausify_out                          false
% 2.63/0.97  --sig_cnt_out                           false
% 2.63/0.97  --trig_cnt_out                          false
% 2.63/0.97  --trig_cnt_out_tolerance                1.
% 2.63/0.97  --trig_cnt_out_sk_spl                   false
% 2.63/0.97  --abstr_cl_out                          false
% 2.63/0.97  
% 2.63/0.97  ------ Global Options
% 2.63/0.97  
% 2.63/0.97  --schedule                              default
% 2.63/0.97  --add_important_lit                     false
% 2.63/0.97  --prop_solver_per_cl                    1000
% 2.63/0.97  --min_unsat_core                        false
% 2.63/0.97  --soft_assumptions                      false
% 2.63/0.97  --soft_lemma_size                       3
% 2.63/0.97  --prop_impl_unit_size                   0
% 2.63/0.97  --prop_impl_unit                        []
% 2.63/0.97  --share_sel_clauses                     true
% 2.63/0.97  --reset_solvers                         false
% 2.63/0.97  --bc_imp_inh                            [conj_cone]
% 2.63/0.97  --conj_cone_tolerance                   3.
% 2.63/0.97  --extra_neg_conj                        none
% 2.63/0.97  --large_theory_mode                     true
% 2.63/0.97  --prolific_symb_bound                   200
% 2.63/0.97  --lt_threshold                          2000
% 2.63/0.97  --clause_weak_htbl                      true
% 2.63/0.97  --gc_record_bc_elim                     false
% 2.63/0.97  
% 2.63/0.97  ------ Preprocessing Options
% 2.63/0.97  
% 2.63/0.97  --preprocessing_flag                    true
% 2.63/0.97  --time_out_prep_mult                    0.1
% 2.63/0.97  --splitting_mode                        input
% 2.63/0.97  --splitting_grd                         true
% 2.63/0.97  --splitting_cvd                         false
% 2.63/0.97  --splitting_cvd_svl                     false
% 2.63/0.97  --splitting_nvd                         32
% 2.63/0.97  --sub_typing                            true
% 2.63/0.97  --prep_gs_sim                           true
% 2.63/0.97  --prep_unflatten                        true
% 2.63/0.97  --prep_res_sim                          true
% 2.63/0.97  --prep_upred                            true
% 2.63/0.97  --prep_sem_filter                       exhaustive
% 2.63/0.97  --prep_sem_filter_out                   false
% 2.63/0.97  --pred_elim                             true
% 2.63/0.97  --res_sim_input                         true
% 2.63/0.97  --eq_ax_congr_red                       true
% 2.63/0.97  --pure_diseq_elim                       true
% 2.63/0.97  --brand_transform                       false
% 2.63/0.97  --non_eq_to_eq                          false
% 2.63/0.97  --prep_def_merge                        true
% 2.63/0.97  --prep_def_merge_prop_impl              false
% 2.63/0.97  --prep_def_merge_mbd                    true
% 2.63/0.97  --prep_def_merge_tr_red                 false
% 2.63/0.97  --prep_def_merge_tr_cl                  false
% 2.63/0.97  --smt_preprocessing                     true
% 2.63/0.97  --smt_ac_axioms                         fast
% 2.63/0.97  --preprocessed_out                      false
% 2.63/0.97  --preprocessed_stats                    false
% 2.63/0.97  
% 2.63/0.97  ------ Abstraction refinement Options
% 2.63/0.97  
% 2.63/0.97  --abstr_ref                             []
% 2.63/0.97  --abstr_ref_prep                        false
% 2.63/0.97  --abstr_ref_until_sat                   false
% 2.63/0.97  --abstr_ref_sig_restrict                funpre
% 2.63/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/0.97  --abstr_ref_under                       []
% 2.63/0.97  
% 2.63/0.97  ------ SAT Options
% 2.63/0.97  
% 2.63/0.97  --sat_mode                              false
% 2.63/0.97  --sat_fm_restart_options                ""
% 2.63/0.97  --sat_gr_def                            false
% 2.63/0.97  --sat_epr_types                         true
% 2.63/0.97  --sat_non_cyclic_types                  false
% 2.63/0.97  --sat_finite_models                     false
% 2.63/0.97  --sat_fm_lemmas                         false
% 2.63/0.97  --sat_fm_prep                           false
% 2.63/0.97  --sat_fm_uc_incr                        true
% 2.63/0.97  --sat_out_model                         small
% 2.63/0.97  --sat_out_clauses                       false
% 2.63/0.97  
% 2.63/0.97  ------ QBF Options
% 2.63/0.97  
% 2.63/0.97  --qbf_mode                              false
% 2.63/0.97  --qbf_elim_univ                         false
% 2.63/0.97  --qbf_dom_inst                          none
% 2.63/0.97  --qbf_dom_pre_inst                      false
% 2.63/0.97  --qbf_sk_in                             false
% 2.63/0.97  --qbf_pred_elim                         true
% 2.63/0.97  --qbf_split                             512
% 2.63/0.97  
% 2.63/0.97  ------ BMC1 Options
% 2.63/0.97  
% 2.63/0.97  --bmc1_incremental                      false
% 2.63/0.97  --bmc1_axioms                           reachable_all
% 2.63/0.97  --bmc1_min_bound                        0
% 2.63/0.97  --bmc1_max_bound                        -1
% 2.63/0.97  --bmc1_max_bound_default                -1
% 2.63/0.97  --bmc1_symbol_reachability              true
% 2.63/0.97  --bmc1_property_lemmas                  false
% 2.63/0.97  --bmc1_k_induction                      false
% 2.63/0.97  --bmc1_non_equiv_states                 false
% 2.63/0.97  --bmc1_deadlock                         false
% 2.63/0.97  --bmc1_ucm                              false
% 2.63/0.97  --bmc1_add_unsat_core                   none
% 2.63/0.97  --bmc1_unsat_core_children              false
% 2.63/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/0.97  --bmc1_out_stat                         full
% 2.63/0.97  --bmc1_ground_init                      false
% 2.63/0.97  --bmc1_pre_inst_next_state              false
% 2.63/0.97  --bmc1_pre_inst_state                   false
% 2.63/0.97  --bmc1_pre_inst_reach_state             false
% 2.63/0.97  --bmc1_out_unsat_core                   false
% 2.63/0.97  --bmc1_aig_witness_out                  false
% 2.63/0.97  --bmc1_verbose                          false
% 2.63/0.97  --bmc1_dump_clauses_tptp                false
% 2.63/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.63/0.97  --bmc1_dump_file                        -
% 2.63/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.63/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.63/0.97  --bmc1_ucm_extend_mode                  1
% 2.63/0.97  --bmc1_ucm_init_mode                    2
% 2.63/0.97  --bmc1_ucm_cone_mode                    none
% 2.63/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.63/0.97  --bmc1_ucm_relax_model                  4
% 2.63/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.63/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/0.97  --bmc1_ucm_layered_model                none
% 2.63/0.97  --bmc1_ucm_max_lemma_size               10
% 2.63/0.97  
% 2.63/0.97  ------ AIG Options
% 2.63/0.97  
% 2.63/0.97  --aig_mode                              false
% 2.63/0.97  
% 2.63/0.97  ------ Instantiation Options
% 2.63/0.97  
% 2.63/0.97  --instantiation_flag                    true
% 2.63/0.97  --inst_sos_flag                         false
% 2.63/0.97  --inst_sos_phase                        true
% 2.63/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/0.97  --inst_lit_sel_side                     num_symb
% 2.63/0.97  --inst_solver_per_active                1400
% 2.63/0.97  --inst_solver_calls_frac                1.
% 2.63/0.97  --inst_passive_queue_type               priority_queues
% 2.63/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/0.97  --inst_passive_queues_freq              [25;2]
% 2.63/0.97  --inst_dismatching                      true
% 2.63/0.97  --inst_eager_unprocessed_to_passive     true
% 2.63/0.97  --inst_prop_sim_given                   true
% 2.63/0.97  --inst_prop_sim_new                     false
% 2.63/0.97  --inst_subs_new                         false
% 2.63/0.97  --inst_eq_res_simp                      false
% 2.63/0.97  --inst_subs_given                       false
% 2.63/0.97  --inst_orphan_elimination               true
% 2.63/0.97  --inst_learning_loop_flag               true
% 2.63/0.97  --inst_learning_start                   3000
% 2.63/0.97  --inst_learning_factor                  2
% 2.63/0.97  --inst_start_prop_sim_after_learn       3
% 2.63/0.97  --inst_sel_renew                        solver
% 2.63/0.97  --inst_lit_activity_flag                true
% 2.63/0.97  --inst_restr_to_given                   false
% 2.63/0.97  --inst_activity_threshold               500
% 2.63/0.97  --inst_out_proof                        true
% 2.63/0.97  
% 2.63/0.97  ------ Resolution Options
% 2.63/0.97  
% 2.63/0.97  --resolution_flag                       true
% 2.63/0.97  --res_lit_sel                           adaptive
% 2.63/0.97  --res_lit_sel_side                      none
% 2.63/0.97  --res_ordering                          kbo
% 2.63/0.97  --res_to_prop_solver                    active
% 2.63/0.97  --res_prop_simpl_new                    false
% 2.63/0.97  --res_prop_simpl_given                  true
% 2.63/0.97  --res_passive_queue_type                priority_queues
% 2.63/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/0.97  --res_passive_queues_freq               [15;5]
% 2.63/0.97  --res_forward_subs                      full
% 2.63/0.97  --res_backward_subs                     full
% 2.63/0.97  --res_forward_subs_resolution           true
% 2.63/0.97  --res_backward_subs_resolution          true
% 2.63/0.97  --res_orphan_elimination                true
% 2.63/0.97  --res_time_limit                        2.
% 2.63/0.97  --res_out_proof                         true
% 2.63/0.97  
% 2.63/0.97  ------ Superposition Options
% 2.63/0.97  
% 2.63/0.97  --superposition_flag                    true
% 2.63/0.97  --sup_passive_queue_type                priority_queues
% 2.63/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.63/0.97  --demod_completeness_check              fast
% 2.63/0.97  --demod_use_ground                      true
% 2.63/0.97  --sup_to_prop_solver                    passive
% 2.63/0.97  --sup_prop_simpl_new                    true
% 2.63/0.97  --sup_prop_simpl_given                  true
% 2.63/0.97  --sup_fun_splitting                     false
% 2.63/0.97  --sup_smt_interval                      50000
% 2.63/0.97  
% 2.63/0.97  ------ Superposition Simplification Setup
% 2.63/0.97  
% 2.63/0.97  --sup_indices_passive                   []
% 2.63/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.97  --sup_full_bw                           [BwDemod]
% 2.63/0.97  --sup_immed_triv                        [TrivRules]
% 2.63/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/0.97  --sup_immed_bw_main                     []
% 2.63/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.97  
% 2.85/0.97  ------ Combination Options
% 2.85/0.97  
% 2.85/0.97  --comb_res_mult                         3
% 2.85/0.97  --comb_sup_mult                         2
% 2.85/0.97  --comb_inst_mult                        10
% 2.85/0.97  
% 2.85/0.97  ------ Debug Options
% 2.85/0.97  
% 2.85/0.97  --dbg_backtrace                         false
% 2.85/0.97  --dbg_dump_prop_clauses                 false
% 2.85/0.97  --dbg_dump_prop_clauses_file            -
% 2.85/0.97  --dbg_out_stat                          false
% 2.85/0.97  ------ Parsing...
% 2.85/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.97  ------ Proving...
% 2.85/0.97  ------ Problem Properties 
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  clauses                                 19
% 2.85/0.97  conjectures                             3
% 2.85/0.97  EPR                                     1
% 2.85/0.97  Horn                                    18
% 2.85/0.97  unary                                   9
% 2.85/0.97  binary                                  6
% 2.85/0.97  lits                                    35
% 2.85/0.97  lits eq                                 13
% 2.85/0.97  fd_pure                                 0
% 2.85/0.97  fd_pseudo                               0
% 2.85/0.97  fd_cond                                 2
% 2.85/0.97  fd_pseudo_cond                          1
% 2.85/0.97  AC symbols                              0
% 2.85/0.97  
% 2.85/0.97  ------ Schedule dynamic 5 is on 
% 2.85/0.97  
% 2.85/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  ------ 
% 2.85/0.97  Current options:
% 2.85/0.97  ------ 
% 2.85/0.97  
% 2.85/0.97  ------ Input Options
% 2.85/0.97  
% 2.85/0.97  --out_options                           all
% 2.85/0.97  --tptp_safe_out                         true
% 2.85/0.97  --problem_path                          ""
% 2.85/0.97  --include_path                          ""
% 2.85/0.97  --clausifier                            res/vclausify_rel
% 2.85/0.97  --clausifier_options                    --mode clausify
% 2.85/0.97  --stdin                                 false
% 2.85/0.97  --stats_out                             all
% 2.85/0.97  
% 2.85/0.97  ------ General Options
% 2.85/0.97  
% 2.85/0.97  --fof                                   false
% 2.85/0.97  --time_out_real                         305.
% 2.85/0.97  --time_out_virtual                      -1.
% 2.85/0.97  --symbol_type_check                     false
% 2.85/0.97  --clausify_out                          false
% 2.85/0.97  --sig_cnt_out                           false
% 2.85/0.97  --trig_cnt_out                          false
% 2.85/0.97  --trig_cnt_out_tolerance                1.
% 2.85/0.97  --trig_cnt_out_sk_spl                   false
% 2.85/0.97  --abstr_cl_out                          false
% 2.85/0.97  
% 2.85/0.97  ------ Global Options
% 2.85/0.97  
% 2.85/0.97  --schedule                              default
% 2.85/0.97  --add_important_lit                     false
% 2.85/0.97  --prop_solver_per_cl                    1000
% 2.85/0.97  --min_unsat_core                        false
% 2.85/0.97  --soft_assumptions                      false
% 2.85/0.97  --soft_lemma_size                       3
% 2.85/0.97  --prop_impl_unit_size                   0
% 2.85/0.97  --prop_impl_unit                        []
% 2.85/0.97  --share_sel_clauses                     true
% 2.85/0.97  --reset_solvers                         false
% 2.85/0.97  --bc_imp_inh                            [conj_cone]
% 2.85/0.97  --conj_cone_tolerance                   3.
% 2.85/0.97  --extra_neg_conj                        none
% 2.85/0.97  --large_theory_mode                     true
% 2.85/0.97  --prolific_symb_bound                   200
% 2.85/0.97  --lt_threshold                          2000
% 2.85/0.97  --clause_weak_htbl                      true
% 2.85/0.97  --gc_record_bc_elim                     false
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing Options
% 2.85/0.97  
% 2.85/0.97  --preprocessing_flag                    true
% 2.85/0.97  --time_out_prep_mult                    0.1
% 2.85/0.97  --splitting_mode                        input
% 2.85/0.97  --splitting_grd                         true
% 2.85/0.97  --splitting_cvd                         false
% 2.85/0.97  --splitting_cvd_svl                     false
% 2.85/0.97  --splitting_nvd                         32
% 2.85/0.97  --sub_typing                            true
% 2.85/0.97  --prep_gs_sim                           true
% 2.85/0.97  --prep_unflatten                        true
% 2.85/0.97  --prep_res_sim                          true
% 2.85/0.97  --prep_upred                            true
% 2.85/0.97  --prep_sem_filter                       exhaustive
% 2.85/0.97  --prep_sem_filter_out                   false
% 2.85/0.97  --pred_elim                             true
% 2.85/0.97  --res_sim_input                         true
% 2.85/0.97  --eq_ax_congr_red                       true
% 2.85/0.97  --pure_diseq_elim                       true
% 2.85/0.97  --brand_transform                       false
% 2.85/0.97  --non_eq_to_eq                          false
% 2.85/0.97  --prep_def_merge                        true
% 2.85/0.97  --prep_def_merge_prop_impl              false
% 2.85/0.97  --prep_def_merge_mbd                    true
% 2.85/0.97  --prep_def_merge_tr_red                 false
% 2.85/0.97  --prep_def_merge_tr_cl                  false
% 2.85/0.97  --smt_preprocessing                     true
% 2.85/0.97  --smt_ac_axioms                         fast
% 2.85/0.97  --preprocessed_out                      false
% 2.85/0.97  --preprocessed_stats                    false
% 2.85/0.97  
% 2.85/0.97  ------ Abstraction refinement Options
% 2.85/0.97  
% 2.85/0.97  --abstr_ref                             []
% 2.85/0.97  --abstr_ref_prep                        false
% 2.85/0.97  --abstr_ref_until_sat                   false
% 2.85/0.97  --abstr_ref_sig_restrict                funpre
% 2.85/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.97  --abstr_ref_under                       []
% 2.85/0.97  
% 2.85/0.97  ------ SAT Options
% 2.85/0.97  
% 2.85/0.97  --sat_mode                              false
% 2.85/0.97  --sat_fm_restart_options                ""
% 2.85/0.97  --sat_gr_def                            false
% 2.85/0.97  --sat_epr_types                         true
% 2.85/0.97  --sat_non_cyclic_types                  false
% 2.85/0.97  --sat_finite_models                     false
% 2.85/0.97  --sat_fm_lemmas                         false
% 2.85/0.97  --sat_fm_prep                           false
% 2.85/0.97  --sat_fm_uc_incr                        true
% 2.85/0.97  --sat_out_model                         small
% 2.85/0.97  --sat_out_clauses                       false
% 2.85/0.97  
% 2.85/0.97  ------ QBF Options
% 2.85/0.97  
% 2.85/0.97  --qbf_mode                              false
% 2.85/0.97  --qbf_elim_univ                         false
% 2.85/0.97  --qbf_dom_inst                          none
% 2.85/0.97  --qbf_dom_pre_inst                      false
% 2.85/0.97  --qbf_sk_in                             false
% 2.85/0.97  --qbf_pred_elim                         true
% 2.85/0.97  --qbf_split                             512
% 2.85/0.97  
% 2.85/0.97  ------ BMC1 Options
% 2.85/0.97  
% 2.85/0.97  --bmc1_incremental                      false
% 2.85/0.97  --bmc1_axioms                           reachable_all
% 2.85/0.97  --bmc1_min_bound                        0
% 2.85/0.97  --bmc1_max_bound                        -1
% 2.85/0.97  --bmc1_max_bound_default                -1
% 2.85/0.97  --bmc1_symbol_reachability              true
% 2.85/0.97  --bmc1_property_lemmas                  false
% 2.85/0.97  --bmc1_k_induction                      false
% 2.85/0.97  --bmc1_non_equiv_states                 false
% 2.85/0.97  --bmc1_deadlock                         false
% 2.85/0.97  --bmc1_ucm                              false
% 2.85/0.97  --bmc1_add_unsat_core                   none
% 2.85/0.97  --bmc1_unsat_core_children              false
% 2.85/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.97  --bmc1_out_stat                         full
% 2.85/0.97  --bmc1_ground_init                      false
% 2.85/0.97  --bmc1_pre_inst_next_state              false
% 2.85/0.97  --bmc1_pre_inst_state                   false
% 2.85/0.97  --bmc1_pre_inst_reach_state             false
% 2.85/0.97  --bmc1_out_unsat_core                   false
% 2.85/0.97  --bmc1_aig_witness_out                  false
% 2.85/0.97  --bmc1_verbose                          false
% 2.85/0.97  --bmc1_dump_clauses_tptp                false
% 2.85/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.97  --bmc1_dump_file                        -
% 2.85/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.97  --bmc1_ucm_extend_mode                  1
% 2.85/0.97  --bmc1_ucm_init_mode                    2
% 2.85/0.97  --bmc1_ucm_cone_mode                    none
% 2.85/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.97  --bmc1_ucm_relax_model                  4
% 2.85/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.97  --bmc1_ucm_layered_model                none
% 2.85/0.97  --bmc1_ucm_max_lemma_size               10
% 2.85/0.97  
% 2.85/0.97  ------ AIG Options
% 2.85/0.97  
% 2.85/0.97  --aig_mode                              false
% 2.85/0.97  
% 2.85/0.97  ------ Instantiation Options
% 2.85/0.97  
% 2.85/0.97  --instantiation_flag                    true
% 2.85/0.97  --inst_sos_flag                         false
% 2.85/0.97  --inst_sos_phase                        true
% 2.85/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.97  --inst_lit_sel_side                     none
% 2.85/0.97  --inst_solver_per_active                1400
% 2.85/0.97  --inst_solver_calls_frac                1.
% 2.85/0.97  --inst_passive_queue_type               priority_queues
% 2.85/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.97  --inst_passive_queues_freq              [25;2]
% 2.85/0.97  --inst_dismatching                      true
% 2.85/0.97  --inst_eager_unprocessed_to_passive     true
% 2.85/0.97  --inst_prop_sim_given                   true
% 2.85/0.97  --inst_prop_sim_new                     false
% 2.85/0.97  --inst_subs_new                         false
% 2.85/0.97  --inst_eq_res_simp                      false
% 2.85/0.97  --inst_subs_given                       false
% 2.85/0.97  --inst_orphan_elimination               true
% 2.85/0.97  --inst_learning_loop_flag               true
% 2.85/0.97  --inst_learning_start                   3000
% 2.85/0.97  --inst_learning_factor                  2
% 2.85/0.97  --inst_start_prop_sim_after_learn       3
% 2.85/0.97  --inst_sel_renew                        solver
% 2.85/0.97  --inst_lit_activity_flag                true
% 2.85/0.97  --inst_restr_to_given                   false
% 2.85/0.97  --inst_activity_threshold               500
% 2.85/0.97  --inst_out_proof                        true
% 2.85/0.97  
% 2.85/0.97  ------ Resolution Options
% 2.85/0.97  
% 2.85/0.97  --resolution_flag                       false
% 2.85/0.97  --res_lit_sel                           adaptive
% 2.85/0.97  --res_lit_sel_side                      none
% 2.85/0.97  --res_ordering                          kbo
% 2.85/0.98  --res_to_prop_solver                    active
% 2.85/0.98  --res_prop_simpl_new                    false
% 2.85/0.98  --res_prop_simpl_given                  true
% 2.85/0.98  --res_passive_queue_type                priority_queues
% 2.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.98  --res_passive_queues_freq               [15;5]
% 2.85/0.98  --res_forward_subs                      full
% 2.85/0.98  --res_backward_subs                     full
% 2.85/0.98  --res_forward_subs_resolution           true
% 2.85/0.98  --res_backward_subs_resolution          true
% 2.85/0.98  --res_orphan_elimination                true
% 2.85/0.98  --res_time_limit                        2.
% 2.85/0.98  --res_out_proof                         true
% 2.85/0.98  
% 2.85/0.98  ------ Superposition Options
% 2.85/0.98  
% 2.85/0.98  --superposition_flag                    true
% 2.85/0.98  --sup_passive_queue_type                priority_queues
% 2.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.98  --demod_completeness_check              fast
% 2.85/0.98  --demod_use_ground                      true
% 2.85/0.98  --sup_to_prop_solver                    passive
% 2.85/0.98  --sup_prop_simpl_new                    true
% 2.85/0.98  --sup_prop_simpl_given                  true
% 2.85/0.98  --sup_fun_splitting                     false
% 2.85/0.98  --sup_smt_interval                      50000
% 2.85/0.98  
% 2.85/0.98  ------ Superposition Simplification Setup
% 2.85/0.98  
% 2.85/0.98  --sup_indices_passive                   []
% 2.85/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_full_bw                           [BwDemod]
% 2.85/0.98  --sup_immed_triv                        [TrivRules]
% 2.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_immed_bw_main                     []
% 2.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.98  
% 2.85/0.98  ------ Combination Options
% 2.85/0.98  
% 2.85/0.98  --comb_res_mult                         3
% 2.85/0.98  --comb_sup_mult                         2
% 2.85/0.98  --comb_inst_mult                        10
% 2.85/0.98  
% 2.85/0.98  ------ Debug Options
% 2.85/0.98  
% 2.85/0.98  --dbg_backtrace                         false
% 2.85/0.98  --dbg_dump_prop_clauses                 false
% 2.85/0.98  --dbg_dump_prop_clauses_file            -
% 2.85/0.98  --dbg_out_stat                          false
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  ------ Proving...
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  % SZS status Theorem for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98   Resolution empty clause
% 2.85/0.98  
% 2.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98  fof(f14,conjecture,(
% 2.85/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f15,negated_conjecture,(
% 2.85/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.85/0.98    inference(negated_conjecture,[],[f14])).
% 2.85/0.98  
% 2.85/0.98  fof(f16,plain,(
% 2.85/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.85/0.98    inference(pure_predicate_removal,[],[f15])).
% 2.85/0.98  
% 2.85/0.98  fof(f29,plain,(
% 2.85/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.85/0.98    inference(ennf_transformation,[],[f16])).
% 2.85/0.98  
% 2.85/0.98  fof(f30,plain,(
% 2.85/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.85/0.98    inference(flattening,[],[f29])).
% 2.85/0.98  
% 2.85/0.98  fof(f35,plain,(
% 2.85/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.85/0.98    introduced(choice_axiom,[])).
% 2.85/0.98  
% 2.85/0.98  fof(f36,plain,(
% 2.85/0.98    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f35])).
% 2.85/0.98  
% 2.85/0.98  fof(f57,plain,(
% 2.85/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.85/0.98    inference(cnf_transformation,[],[f36])).
% 2.85/0.98  
% 2.85/0.98  fof(f1,axiom,(
% 2.85/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f37,plain,(
% 2.85/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f1])).
% 2.85/0.98  
% 2.85/0.98  fof(f65,plain,(
% 2.85/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))),
% 2.85/0.98    inference(definition_unfolding,[],[f57,f37])).
% 2.85/0.98  
% 2.85/0.98  fof(f12,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f17,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.85/0.98    inference(pure_predicate_removal,[],[f12])).
% 2.85/0.98  
% 2.85/0.98  fof(f27,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f17])).
% 2.85/0.98  
% 2.85/0.98  fof(f54,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f27])).
% 2.85/0.98  
% 2.85/0.98  fof(f6,axiom,(
% 2.85/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f20,plain,(
% 2.85/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.85/0.98    inference(ennf_transformation,[],[f6])).
% 2.85/0.98  
% 2.85/0.98  fof(f34,plain,(
% 2.85/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.85/0.98    inference(nnf_transformation,[],[f20])).
% 2.85/0.98  
% 2.85/0.98  fof(f46,plain,(
% 2.85/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f34])).
% 2.85/0.98  
% 2.85/0.98  fof(f11,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f26,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f11])).
% 2.85/0.98  
% 2.85/0.98  fof(f53,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f26])).
% 2.85/0.98  
% 2.85/0.98  fof(f2,axiom,(
% 2.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f19,plain,(
% 2.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.85/0.98    inference(ennf_transformation,[],[f2])).
% 2.85/0.98  
% 2.85/0.98  fof(f31,plain,(
% 2.85/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.85/0.98    inference(nnf_transformation,[],[f19])).
% 2.85/0.98  
% 2.85/0.98  fof(f32,plain,(
% 2.85/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.85/0.98    inference(flattening,[],[f31])).
% 2.85/0.98  
% 2.85/0.98  fof(f38,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f32])).
% 2.85/0.98  
% 2.85/0.98  fof(f62,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.85/0.98    inference(definition_unfolding,[],[f38,f37,f37])).
% 2.85/0.98  
% 2.85/0.98  fof(f41,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 2.85/0.98    inference(cnf_transformation,[],[f32])).
% 2.85/0.98  
% 2.85/0.98  fof(f60,plain,(
% 2.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) != X0) )),
% 2.85/0.98    inference(definition_unfolding,[],[f41,f37])).
% 2.85/0.98  
% 2.85/0.98  fof(f67,plain,(
% 2.85/0.98    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 2.85/0.98    inference(equality_resolution,[],[f60])).
% 2.85/0.98  
% 2.85/0.98  fof(f59,plain,(
% 2.85/0.98    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.85/0.98    inference(cnf_transformation,[],[f36])).
% 2.85/0.98  
% 2.85/0.98  fof(f64,plain,(
% 2.85/0.98    ~r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.85/0.98    inference(definition_unfolding,[],[f59,f37,f37])).
% 2.85/0.98  
% 2.85/0.98  fof(f13,axiom,(
% 2.85/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f28,plain,(
% 2.85/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.98    inference(ennf_transformation,[],[f13])).
% 2.85/0.98  
% 2.85/0.98  fof(f55,plain,(
% 2.85/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f28])).
% 2.85/0.98  
% 2.85/0.98  fof(f7,axiom,(
% 2.85/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f21,plain,(
% 2.85/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.85/0.98    inference(ennf_transformation,[],[f7])).
% 2.85/0.98  
% 2.85/0.98  fof(f48,plain,(
% 2.85/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f21])).
% 2.85/0.98  
% 2.85/0.98  fof(f10,axiom,(
% 2.85/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f24,plain,(
% 2.85/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.85/0.98    inference(ennf_transformation,[],[f10])).
% 2.85/0.98  
% 2.85/0.98  fof(f25,plain,(
% 2.85/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.85/0.98    inference(flattening,[],[f24])).
% 2.85/0.98  
% 2.85/0.98  fof(f52,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f25])).
% 2.85/0.98  
% 2.85/0.98  fof(f63,plain,(
% 2.85/0.98    ( ! [X0,X1] : (k2_tarski(k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_tarski(X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.85/0.98    inference(definition_unfolding,[],[f52,f37,f37])).
% 2.85/0.98  
% 2.85/0.98  fof(f56,plain,(
% 2.85/0.98    v1_funct_1(sK3)),
% 2.85/0.98    inference(cnf_transformation,[],[f36])).
% 2.85/0.98  
% 2.85/0.98  fof(f9,axiom,(
% 2.85/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f22,plain,(
% 2.85/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(ennf_transformation,[],[f9])).
% 2.85/0.98  
% 2.85/0.98  fof(f23,plain,(
% 2.85/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.85/0.98    inference(flattening,[],[f22])).
% 2.85/0.98  
% 2.85/0.98  fof(f50,plain,(
% 2.85/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f23])).
% 2.85/0.98  
% 2.85/0.98  fof(f8,axiom,(
% 2.85/0.98    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f49,plain,(
% 2.85/0.98    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.85/0.98    inference(cnf_transformation,[],[f8])).
% 2.85/0.98  
% 2.85/0.98  fof(f3,axiom,(
% 2.85/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f43,plain,(
% 2.85/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f3])).
% 2.85/0.98  
% 2.85/0.98  fof(f4,axiom,(
% 2.85/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.85/0.98  
% 2.85/0.98  fof(f33,plain,(
% 2.85/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.85/0.98    inference(nnf_transformation,[],[f4])).
% 2.85/0.98  
% 2.85/0.98  fof(f44,plain,(
% 2.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.85/0.98    inference(cnf_transformation,[],[f33])).
% 2.85/0.98  
% 2.85/0.98  cnf(c_20,negated_conjecture,
% 2.85/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) ),
% 2.85/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1838,plain,
% 2.85/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_16,plain,
% 2.85/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.85/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_9,plain,
% 2.85/0.98      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_289,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 2.85/0.98      | ~ v1_relat_1(X0) ),
% 2.85/0.98      inference(resolution,[status(thm)],[c_16,c_9]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_15,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_293,plain,
% 2.85/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 2.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.85/0.98      inference(global_propositional_subsumption,[status(thm)],[c_289,c_15]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_294,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.85/0.98      inference(renaming,[status(thm)],[c_293]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1836,plain,
% 2.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.85/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2089,plain,
% 2.85/0.98      ( r1_tarski(k1_relat_1(sK3),k2_tarski(sK0,sK0)) = iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1838,c_1836]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_4,plain,
% 2.85/0.98      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
% 2.85/0.98      | k2_tarski(X1,X2) = X0
% 2.85/0.98      | k2_tarski(X2,X2) = X0
% 2.85/0.98      | k2_tarski(X1,X1) = X0
% 2.85/0.98      | k1_xboole_0 = X0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1848,plain,
% 2.85/0.98      ( k2_tarski(X0,X1) = X2
% 2.85/0.98      | k2_tarski(X1,X1) = X2
% 2.85/0.98      | k2_tarski(X0,X0) = X2
% 2.85/0.98      | k1_xboole_0 = X2
% 2.85/0.98      | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3248,plain,
% 2.85/0.98      ( k2_tarski(sK0,sK0) = k1_relat_1(sK3) | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_2089,c_1848]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1,plain,
% 2.85/0.98      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
% 2.85/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1851,plain,
% 2.85/0.98      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3354,plain,
% 2.85/0.98      ( k1_relat_1(sK3) = k1_xboole_0
% 2.85/0.98      | r1_tarski(k1_relat_1(sK3),k2_tarski(X0,sK0)) = iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_3248,c_1851]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_18,negated_conjecture,
% 2.85/0.98      ( ~ r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.85/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1983,plain,
% 2.85/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
% 2.85/0.98      | v1_relat_1(sK3) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_17,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.85/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2005,plain,
% 2.85/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
% 2.85/0.98      | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2056,plain,
% 2.85/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1)))
% 2.85/0.98      | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_2005]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1409,plain,
% 2.85/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.85/0.98      theory(equality) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2010,plain,
% 2.85/0.98      ( ~ r1_tarski(X0,X1)
% 2.85/0.98      | r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.85/0.98      | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2) != X0
% 2.85/0.98      | k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_1409]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2055,plain,
% 2.85/0.98      ( r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.85/0.98      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.85/0.98      | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.85/0.98      | k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_2010]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2170,plain,
% 2.85/0.98      ( r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.85/0.98      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.85/0.98      | k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.85/0.98      | k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_2055]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_10,plain,
% 2.85/0.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2171,plain,
% 2.85/0.98      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_14,plain,
% 2.85/0.98      ( ~ v1_funct_1(X0)
% 2.85/0.98      | ~ v1_relat_1(X0)
% 2.85/0.98      | k2_tarski(X1,X1) != k1_relat_1(X0)
% 2.85/0.98      | k2_tarski(k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.85/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_21,negated_conjecture,
% 2.85/0.98      ( v1_funct_1(sK3) ),
% 2.85/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_270,plain,
% 2.85/0.98      ( ~ v1_relat_1(X0)
% 2.85/0.98      | k2_tarski(X1,X1) != k1_relat_1(X0)
% 2.85/0.98      | k2_tarski(k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.85/0.98      | sK3 != X0 ),
% 2.85/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_271,plain,
% 2.85/0.98      ( ~ v1_relat_1(sK3)
% 2.85/0.98      | k2_tarski(X0,X0) != k1_relat_1(sK3)
% 2.85/0.98      | k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.85/0.98      inference(unflattening,[status(thm)],[c_270]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1837,plain,
% 2.85/0.98      ( k2_tarski(X0,X0) != k1_relat_1(sK3)
% 2.85/0.98      | k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.85/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_23,plain,
% 2.85/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_272,plain,
% 2.85/0.98      ( k2_tarski(X0,X0) != k1_relat_1(sK3)
% 2.85/0.98      | k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.85/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1984,plain,
% 2.85/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),sK1))) != iProver_top
% 2.85/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1989,plain,
% 2.85/0.98      ( k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.85/0.98      | k2_tarski(X0,X0) != k1_relat_1(sK3) ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_1837,c_23,c_272,c_1984]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1990,plain,
% 2.85/0.98      ( k2_tarski(X0,X0) != k1_relat_1(sK3)
% 2.85/0.98      | k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.85/0.98      inference(renaming,[status(thm)],[c_1989]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3356,plain,
% 2.85/0.98      ( k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.85/0.98      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_3248,c_1990]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3417,plain,
% 2.85/0.98      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_3354,c_20,c_18,c_1983,c_2056,c_2170,c_2171,c_3356]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_13,plain,
% 2.85/0.98      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1842,plain,
% 2.85/0.98      ( k1_relat_1(X0) != k1_xboole_0
% 2.85/0.98      | k1_xboole_0 = X0
% 2.85/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3429,plain,
% 2.85/0.98      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_3417,c_1842]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1406,plain,( X0 = X0 ),theory(equality) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2542,plain,
% 2.85/0.98      ( sK3 = sK3 ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_1406]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2769,plain,
% 2.85/0.98      ( ~ v1_relat_1(sK3)
% 2.85/0.98      | k1_relat_1(sK3) != k1_xboole_0
% 2.85/0.98      | k1_xboole_0 = sK3 ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1407,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2543,plain,
% 2.85/0.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_1407]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3130,plain,
% 2.85/0.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_2543]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3131,plain,
% 2.85/0.98      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.85/0.98      inference(instantiation,[status(thm)],[c_3130]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3476,plain,
% 2.85/0.98      ( sK3 = k1_xboole_0 ),
% 2.85/0.98      inference(global_propositional_subsumption,
% 2.85/0.98                [status(thm)],
% 2.85/0.98                [c_3429,c_20,c_18,c_1983,c_2056,c_2170,c_2171,c_2542,c_2769,
% 2.85/0.98                 c_3131,c_3356]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1840,plain,
% 2.85/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.85/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2691,plain,
% 2.85/0.98      ( k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1838,c_1840]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1839,plain,
% 2.85/0.98      ( r1_tarski(k7_relset_1(k2_tarski(sK0,sK0),sK1,sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2890,plain,
% 2.85/0.98      ( r1_tarski(k9_relat_1(sK3,sK2),k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_2691,c_1839]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3480,plain,
% 2.85/0.98      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_tarski(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_3476,c_2890]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_11,plain,
% 2.85/0.98      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.85/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3490,plain,
% 2.85/0.98      ( r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.85/0.98      inference(demodulation,[status(thm)],[c_3480,c_11]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_5,plain,
% 2.85/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.85/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1847,plain,
% 2.85/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_7,plain,
% 2.85/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.85/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_1845,plain,
% 2.85/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.85/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.85/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_2197,plain,
% 2.85/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.85/0.98      inference(superposition,[status(thm)],[c_1847,c_1845]) ).
% 2.85/0.98  
% 2.85/0.98  cnf(c_3577,plain,
% 2.85/0.98      ( $false ),
% 2.85/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_3490,c_2197]) ).
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/0.98  
% 2.85/0.98  ------                               Statistics
% 2.85/0.98  
% 2.85/0.98  ------ General
% 2.85/0.98  
% 2.85/0.98  abstr_ref_over_cycles:                  0
% 2.85/0.98  abstr_ref_under_cycles:                 0
% 2.85/0.98  gc_basic_clause_elim:                   0
% 2.85/0.98  forced_gc_time:                         0
% 2.85/0.98  parsing_time:                           0.01
% 2.85/0.98  unif_index_cands_time:                  0.
% 2.85/0.98  unif_index_add_time:                    0.
% 2.85/0.98  orderings_time:                         0.
% 2.85/0.98  out_proof_time:                         0.009
% 2.85/0.98  total_time:                             0.123
% 2.85/0.98  num_of_symbols:                         49
% 2.85/0.98  num_of_terms:                           2311
% 2.85/0.98  
% 2.85/0.98  ------ Preprocessing
% 2.85/0.98  
% 2.85/0.98  num_of_splits:                          0
% 2.85/0.98  num_of_split_atoms:                     0
% 2.85/0.98  num_of_reused_defs:                     0
% 2.85/0.98  num_eq_ax_congr_red:                    8
% 2.85/0.98  num_of_sem_filtered_clauses:            1
% 2.85/0.98  num_of_subtypes:                        0
% 2.85/0.98  monotx_restored_types:                  0
% 2.85/0.98  sat_num_of_epr_types:                   0
% 2.85/0.98  sat_num_of_non_cyclic_types:            0
% 2.85/0.98  sat_guarded_non_collapsed_types:        0
% 2.85/0.98  num_pure_diseq_elim:                    0
% 2.85/0.98  simp_replaced_by:                       0
% 2.85/0.98  res_preprocessed:                       106
% 2.85/0.98  prep_upred:                             0
% 2.85/0.98  prep_unflattend:                        73
% 2.85/0.98  smt_new_axioms:                         0
% 2.85/0.98  pred_elim_cands:                        3
% 2.85/0.98  pred_elim:                              2
% 2.85/0.98  pred_elim_cl:                           3
% 2.85/0.98  pred_elim_cycles:                       8
% 2.85/0.98  merged_defs:                            8
% 2.85/0.98  merged_defs_ncl:                        0
% 2.85/0.98  bin_hyper_res:                          8
% 2.85/0.98  prep_cycles:                            4
% 2.85/0.98  pred_elim_time:                         0.016
% 2.85/0.98  splitting_time:                         0.
% 2.85/0.98  sem_filter_time:                        0.
% 2.85/0.98  monotx_time:                            0.
% 2.85/0.98  subtype_inf_time:                       0.
% 2.85/0.98  
% 2.85/0.98  ------ Problem properties
% 2.85/0.98  
% 2.85/0.98  clauses:                                19
% 2.85/0.98  conjectures:                            3
% 2.85/0.98  epr:                                    1
% 2.85/0.98  horn:                                   18
% 2.85/0.98  ground:                                 3
% 2.85/0.98  unary:                                  9
% 2.85/0.98  binary:                                 6
% 2.85/0.98  lits:                                   35
% 2.85/0.98  lits_eq:                                13
% 2.85/0.98  fd_pure:                                0
% 2.85/0.98  fd_pseudo:                              0
% 2.85/0.98  fd_cond:                                2
% 2.85/0.98  fd_pseudo_cond:                         1
% 2.85/0.98  ac_symbols:                             0
% 2.85/0.98  
% 2.85/0.98  ------ Propositional Solver
% 2.85/0.98  
% 2.85/0.98  prop_solver_calls:                      27
% 2.85/0.98  prop_fast_solver_calls:                 698
% 2.85/0.98  smt_solver_calls:                       0
% 2.85/0.98  smt_fast_solver_calls:                  0
% 2.85/0.98  prop_num_of_clauses:                    926
% 2.85/0.98  prop_preprocess_simplified:             4053
% 2.85/0.98  prop_fo_subsumed:                       6
% 2.85/0.98  prop_solver_time:                       0.
% 2.85/0.98  smt_solver_time:                        0.
% 2.85/0.98  smt_fast_solver_time:                   0.
% 2.85/0.98  prop_fast_solver_time:                  0.
% 2.85/0.98  prop_unsat_core_time:                   0.
% 2.85/0.98  
% 2.85/0.98  ------ QBF
% 2.85/0.98  
% 2.85/0.98  qbf_q_res:                              0
% 2.85/0.98  qbf_num_tautologies:                    0
% 2.85/0.98  qbf_prep_cycles:                        0
% 2.85/0.98  
% 2.85/0.98  ------ BMC1
% 2.85/0.98  
% 2.85/0.98  bmc1_current_bound:                     -1
% 2.85/0.98  bmc1_last_solved_bound:                 -1
% 2.85/0.98  bmc1_unsat_core_size:                   -1
% 2.85/0.98  bmc1_unsat_core_parents_size:           -1
% 2.85/0.98  bmc1_merge_next_fun:                    0
% 2.85/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.85/0.98  
% 2.85/0.98  ------ Instantiation
% 2.85/0.98  
% 2.85/0.98  inst_num_of_clauses:                    257
% 2.85/0.98  inst_num_in_passive:                    1
% 2.85/0.98  inst_num_in_active:                     201
% 2.85/0.98  inst_num_in_unprocessed:                55
% 2.85/0.98  inst_num_of_loops:                      210
% 2.85/0.98  inst_num_of_learning_restarts:          0
% 2.85/0.98  inst_num_moves_active_passive:          6
% 2.85/0.98  inst_lit_activity:                      0
% 2.85/0.98  inst_lit_activity_moves:                0
% 2.85/0.98  inst_num_tautologies:                   0
% 2.85/0.98  inst_num_prop_implied:                  0
% 2.85/0.98  inst_num_existing_simplified:           0
% 2.85/0.98  inst_num_eq_res_simplified:             0
% 2.85/0.98  inst_num_child_elim:                    0
% 2.85/0.98  inst_num_of_dismatching_blockings:      61
% 2.85/0.98  inst_num_of_non_proper_insts:           314
% 2.85/0.98  inst_num_of_duplicates:                 0
% 2.85/0.98  inst_inst_num_from_inst_to_res:         0
% 2.85/0.98  inst_dismatching_checking_time:         0.
% 2.85/0.98  
% 2.85/0.98  ------ Resolution
% 2.85/0.98  
% 2.85/0.98  res_num_of_clauses:                     0
% 2.85/0.98  res_num_in_passive:                     0
% 2.85/0.98  res_num_in_active:                      0
% 2.85/0.98  res_num_of_loops:                       110
% 2.85/0.98  res_forward_subset_subsumed:            28
% 2.85/0.98  res_backward_subset_subsumed:           2
% 2.85/0.98  res_forward_subsumed:                   2
% 2.85/0.98  res_backward_subsumed:                  0
% 2.85/0.98  res_forward_subsumption_resolution:     0
% 2.85/0.98  res_backward_subsumption_resolution:    0
% 2.85/0.98  res_clause_to_clause_subsumption:       136
% 2.85/0.98  res_orphan_elimination:                 0
% 2.85/0.98  res_tautology_del:                      55
% 2.85/0.98  res_num_eq_res_simplified:              0
% 2.85/0.98  res_num_sel_changes:                    0
% 2.85/0.98  res_moves_from_active_to_pass:          0
% 2.85/0.98  
% 2.85/0.98  ------ Superposition
% 2.85/0.98  
% 2.85/0.98  sup_time_total:                         0.
% 2.85/0.98  sup_time_generating:                    0.
% 2.85/0.98  sup_time_sim_full:                      0.
% 2.85/0.98  sup_time_sim_immed:                     0.
% 2.85/0.98  
% 2.85/0.98  sup_num_of_clauses:                     40
% 2.85/0.98  sup_num_in_active:                      30
% 2.85/0.98  sup_num_in_passive:                     10
% 2.85/0.98  sup_num_of_loops:                       40
% 2.85/0.98  sup_fw_superposition:                   31
% 2.85/0.98  sup_bw_superposition:                   20
% 2.85/0.98  sup_immediate_simplified:               8
% 2.85/0.98  sup_given_eliminated:                   0
% 2.85/0.98  comparisons_done:                       0
% 2.85/0.98  comparisons_avoided:                    0
% 2.85/0.98  
% 2.85/0.98  ------ Simplifications
% 2.85/0.98  
% 2.85/0.98  
% 2.85/0.98  sim_fw_subset_subsumed:                 0
% 2.85/0.98  sim_bw_subset_subsumed:                 5
% 2.85/0.98  sim_fw_subsumed:                        6
% 2.85/0.98  sim_bw_subsumed:                        0
% 2.85/0.98  sim_fw_subsumption_res:                 1
% 2.85/0.98  sim_bw_subsumption_res:                 0
% 2.85/0.98  sim_tautology_del:                      1
% 2.85/0.98  sim_eq_tautology_del:                   5
% 2.85/0.98  sim_eq_res_simp:                        0
% 2.85/0.98  sim_fw_demodulated:                     2
% 2.85/0.98  sim_bw_demodulated:                     10
% 2.85/0.98  sim_light_normalised:                   2
% 2.85/0.98  sim_joinable_taut:                      0
% 2.85/0.98  sim_joinable_simp:                      0
% 2.85/0.98  sim_ac_normalised:                      0
% 2.85/0.98  sim_smt_subsumption:                    0
% 2.85/0.98  
%------------------------------------------------------------------------------
