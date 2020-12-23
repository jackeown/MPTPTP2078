%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:42 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 730 expanded)
%              Number of clauses        :   94 ( 221 expanded)
%              Number of leaves         :   21 ( 162 expanded)
%              Depth                    :   23
%              Number of atoms          :  338 (1659 expanded)
%              Number of equality atoms :  186 ( 655 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f37,plain,
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

fof(f38,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f37])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f62])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f61,f63,f63])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f63,f63])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f43,f63,f63])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_7])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_14,c_13,c_7])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_268,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_18])).

cnf(c_269,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_814,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k7_relat_1(sK3,X0_47) = sK3 ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_1191,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_814])).

cnf(c_286,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_287,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_812,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_287])).

cnf(c_1096,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_833,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1192,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1195,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1196,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1195])).

cnf(c_1251,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1096,c_1192,c_1196])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_825,plain,
    ( ~ v1_relat_1(X0_47)
    | k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1090,plain,
    ( k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47)
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_1668,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_47)) = k9_relat_1(sK3,X0_47) ),
    inference(superposition,[status(thm)],[c_1251,c_1090])).

cnf(c_1845,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1191,c_1668])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_822,plain,
    ( ~ v1_relat_1(X0_47)
    | k2_relat_1(X0_47) != k1_xboole_0
    | k1_xboole_0 = X0_47 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1091,plain,
    ( k2_relat_1(X0_47) != k1_xboole_0
    | k1_xboole_0 = X0_47
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_1846,plain,
    ( k7_relat_1(sK3,X0_47) = k1_xboole_0
    | k9_relat_1(sK3,X0_47) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,X0_47)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1668,c_1091])).

cnf(c_2122,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1845,c_1846])).

cnf(c_2123,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2122,c_1191])).

cnf(c_2124,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2123,c_1191])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_277,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_278,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_813,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k7_relset_1(X0_47,X1_47,sK3,X2_47) = k9_relat_1(sK3,X2_47) ),
    inference(subtyping,[status(esa)],[c_278])).

cnf(c_1193,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_1284,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_838,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_1234,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0_47
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1_47 ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_1285,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0_47)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_1338,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_826,plain,
    ( r1_tarski(k9_relat_1(X0_47,X1_47),k2_relat_1(X0_47))
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1339,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_832,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1567,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_12,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_203,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_204,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_818,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50)))
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_1094,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_880,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1387,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1094,c_880,c_1192,c_1196])).

cnf(c_1394,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1387])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_827,plain,
    ( ~ r1_tarski(X0_47,k2_enumset1(X0_50,X0_50,X0_50,X0_50))
    | k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_47
    | k1_xboole_0 = X0_47 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1088,plain,
    ( k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_47
    | k1_xboole_0 = X0_47
    | r1_tarski(X0_47,k2_enumset1(X0_50,X0_50,X0_50,X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_1683,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1394,c_1088])).

cnf(c_1802,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_836,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1569,plain,
    ( X0_47 != X1_47
    | sK3 != X1_47
    | sK3 = X0_47 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_1917,plain,
    ( X0_47 != sK3
    | sK3 = X0_47
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1569])).

cnf(c_1918,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_2127,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2124,c_16,c_1192,c_1195,c_1284,c_1338,c_1339,c_1567,c_1683,c_1802,c_1918])).

cnf(c_1220,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
    inference(equality_resolution,[status(thm)],[c_813])).

cnf(c_820,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1093,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_1241,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1220,c_1093])).

cnf(c_2137,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2127,c_1241])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_256,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_257,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_815,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_257])).

cnf(c_1095,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_1199,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_1201,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1199])).

cnf(c_1200,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) = k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1533,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1095,c_1201,c_1200])).

cnf(c_1667,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0_47)) = k9_relat_1(k1_xboole_0,X0_47) ),
    inference(superposition,[status(thm)],[c_1533,c_1090])).

cnf(c_8,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_824,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_238,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_222])).

cnf(c_239,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_817,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
    | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_1312,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_1538,plain,
    ( k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_1200,c_1312])).

cnf(c_1672,plain,
    ( k9_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1667,c_824,c_1538])).

cnf(c_2151,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2137,c_1672])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_830,plain,
    ( r1_tarski(k1_xboole_0,X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1085,plain,
    ( r1_tarski(k1_xboole_0,X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_2245,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2151,c_1085])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:23:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.80/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/0.98  
% 1.80/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.80/0.98  
% 1.80/0.98  ------  iProver source info
% 1.80/0.98  
% 1.80/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.80/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.80/0.98  git: non_committed_changes: false
% 1.80/0.98  git: last_make_outside_of_git: false
% 1.80/0.98  
% 1.80/0.98  ------ 
% 1.80/0.98  
% 1.80/0.98  ------ Input Options
% 1.80/0.98  
% 1.80/0.98  --out_options                           all
% 1.80/0.98  --tptp_safe_out                         true
% 1.80/0.98  --problem_path                          ""
% 1.80/0.98  --include_path                          ""
% 1.80/0.98  --clausifier                            res/vclausify_rel
% 1.80/0.98  --clausifier_options                    --mode clausify
% 1.80/0.98  --stdin                                 false
% 1.80/0.98  --stats_out                             all
% 1.80/0.98  
% 1.80/0.98  ------ General Options
% 1.80/0.98  
% 1.80/0.98  --fof                                   false
% 1.80/0.98  --time_out_real                         305.
% 1.80/0.98  --time_out_virtual                      -1.
% 1.80/0.98  --symbol_type_check                     false
% 1.80/0.98  --clausify_out                          false
% 1.80/0.98  --sig_cnt_out                           false
% 1.80/0.98  --trig_cnt_out                          false
% 1.80/0.98  --trig_cnt_out_tolerance                1.
% 1.80/0.98  --trig_cnt_out_sk_spl                   false
% 1.80/0.98  --abstr_cl_out                          false
% 1.80/0.98  
% 1.80/0.98  ------ Global Options
% 1.80/0.98  
% 1.80/0.98  --schedule                              default
% 1.80/0.98  --add_important_lit                     false
% 1.80/0.98  --prop_solver_per_cl                    1000
% 1.80/0.98  --min_unsat_core                        false
% 1.80/0.98  --soft_assumptions                      false
% 1.80/0.98  --soft_lemma_size                       3
% 1.80/0.98  --prop_impl_unit_size                   0
% 1.80/0.98  --prop_impl_unit                        []
% 1.80/0.98  --share_sel_clauses                     true
% 1.80/0.98  --reset_solvers                         false
% 1.80/0.98  --bc_imp_inh                            [conj_cone]
% 1.80/0.98  --conj_cone_tolerance                   3.
% 1.80/0.98  --extra_neg_conj                        none
% 1.80/0.98  --large_theory_mode                     true
% 1.80/0.98  --prolific_symb_bound                   200
% 1.80/0.98  --lt_threshold                          2000
% 1.80/0.98  --clause_weak_htbl                      true
% 1.80/0.98  --gc_record_bc_elim                     false
% 1.80/0.98  
% 1.80/0.98  ------ Preprocessing Options
% 1.80/0.98  
% 1.80/0.98  --preprocessing_flag                    true
% 1.80/0.98  --time_out_prep_mult                    0.1
% 1.80/0.98  --splitting_mode                        input
% 1.80/0.98  --splitting_grd                         true
% 1.80/0.98  --splitting_cvd                         false
% 1.80/0.98  --splitting_cvd_svl                     false
% 1.80/0.98  --splitting_nvd                         32
% 1.80/0.98  --sub_typing                            true
% 1.80/0.98  --prep_gs_sim                           true
% 1.80/0.98  --prep_unflatten                        true
% 1.80/0.98  --prep_res_sim                          true
% 1.80/0.98  --prep_upred                            true
% 1.80/0.98  --prep_sem_filter                       exhaustive
% 1.80/0.98  --prep_sem_filter_out                   false
% 1.80/0.98  --pred_elim                             true
% 1.80/0.98  --res_sim_input                         true
% 1.80/0.98  --eq_ax_congr_red                       true
% 1.80/0.98  --pure_diseq_elim                       true
% 1.80/0.98  --brand_transform                       false
% 1.80/0.98  --non_eq_to_eq                          false
% 1.80/0.98  --prep_def_merge                        true
% 1.80/0.98  --prep_def_merge_prop_impl              false
% 1.80/0.98  --prep_def_merge_mbd                    true
% 1.80/0.98  --prep_def_merge_tr_red                 false
% 1.80/0.98  --prep_def_merge_tr_cl                  false
% 1.80/0.98  --smt_preprocessing                     true
% 1.80/0.98  --smt_ac_axioms                         fast
% 1.80/0.98  --preprocessed_out                      false
% 1.80/0.98  --preprocessed_stats                    false
% 1.80/0.98  
% 1.80/0.98  ------ Abstraction refinement Options
% 1.80/0.98  
% 1.80/0.98  --abstr_ref                             []
% 1.80/0.98  --abstr_ref_prep                        false
% 1.80/0.98  --abstr_ref_until_sat                   false
% 1.80/0.98  --abstr_ref_sig_restrict                funpre
% 1.80/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/0.98  --abstr_ref_under                       []
% 1.80/0.98  
% 1.80/0.98  ------ SAT Options
% 1.80/0.98  
% 1.80/0.98  --sat_mode                              false
% 1.80/0.98  --sat_fm_restart_options                ""
% 1.80/0.98  --sat_gr_def                            false
% 1.80/0.98  --sat_epr_types                         true
% 1.80/0.98  --sat_non_cyclic_types                  false
% 1.80/0.98  --sat_finite_models                     false
% 1.80/0.98  --sat_fm_lemmas                         false
% 1.80/0.98  --sat_fm_prep                           false
% 1.80/0.98  --sat_fm_uc_incr                        true
% 1.80/0.98  --sat_out_model                         small
% 1.80/0.98  --sat_out_clauses                       false
% 1.80/0.98  
% 1.80/0.98  ------ QBF Options
% 1.80/0.98  
% 1.80/0.98  --qbf_mode                              false
% 1.80/0.98  --qbf_elim_univ                         false
% 1.80/0.98  --qbf_dom_inst                          none
% 1.80/0.98  --qbf_dom_pre_inst                      false
% 1.80/0.98  --qbf_sk_in                             false
% 1.80/0.98  --qbf_pred_elim                         true
% 1.80/0.98  --qbf_split                             512
% 1.80/0.98  
% 1.80/0.98  ------ BMC1 Options
% 1.80/0.98  
% 1.80/0.98  --bmc1_incremental                      false
% 1.80/0.98  --bmc1_axioms                           reachable_all
% 1.80/0.98  --bmc1_min_bound                        0
% 1.80/0.98  --bmc1_max_bound                        -1
% 1.80/0.98  --bmc1_max_bound_default                -1
% 1.80/0.98  --bmc1_symbol_reachability              true
% 1.80/0.98  --bmc1_property_lemmas                  false
% 1.80/0.98  --bmc1_k_induction                      false
% 1.80/0.98  --bmc1_non_equiv_states                 false
% 1.80/0.98  --bmc1_deadlock                         false
% 1.80/0.98  --bmc1_ucm                              false
% 1.80/0.98  --bmc1_add_unsat_core                   none
% 1.80/0.98  --bmc1_unsat_core_children              false
% 1.80/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/0.98  --bmc1_out_stat                         full
% 1.80/0.98  --bmc1_ground_init                      false
% 1.80/0.98  --bmc1_pre_inst_next_state              false
% 1.80/0.98  --bmc1_pre_inst_state                   false
% 1.80/0.98  --bmc1_pre_inst_reach_state             false
% 1.80/0.98  --bmc1_out_unsat_core                   false
% 1.80/0.98  --bmc1_aig_witness_out                  false
% 1.80/0.98  --bmc1_verbose                          false
% 1.80/0.98  --bmc1_dump_clauses_tptp                false
% 1.80/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.80/0.98  --bmc1_dump_file                        -
% 1.80/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.80/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.80/0.98  --bmc1_ucm_extend_mode                  1
% 1.80/0.98  --bmc1_ucm_init_mode                    2
% 1.80/0.98  --bmc1_ucm_cone_mode                    none
% 1.80/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.80/0.98  --bmc1_ucm_relax_model                  4
% 1.80/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.80/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/0.98  --bmc1_ucm_layered_model                none
% 1.80/0.98  --bmc1_ucm_max_lemma_size               10
% 1.80/0.98  
% 1.80/0.98  ------ AIG Options
% 1.80/0.98  
% 1.80/0.98  --aig_mode                              false
% 1.80/0.98  
% 1.80/0.98  ------ Instantiation Options
% 1.80/0.98  
% 1.80/0.98  --instantiation_flag                    true
% 1.80/0.98  --inst_sos_flag                         false
% 1.80/0.98  --inst_sos_phase                        true
% 1.80/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/0.98  --inst_lit_sel_side                     num_symb
% 1.80/0.98  --inst_solver_per_active                1400
% 1.80/0.98  --inst_solver_calls_frac                1.
% 1.80/0.98  --inst_passive_queue_type               priority_queues
% 1.80/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/0.98  --inst_passive_queues_freq              [25;2]
% 1.80/0.98  --inst_dismatching                      true
% 1.80/0.98  --inst_eager_unprocessed_to_passive     true
% 1.80/0.98  --inst_prop_sim_given                   true
% 1.80/0.98  --inst_prop_sim_new                     false
% 1.80/0.98  --inst_subs_new                         false
% 1.80/0.98  --inst_eq_res_simp                      false
% 1.80/0.98  --inst_subs_given                       false
% 1.80/0.98  --inst_orphan_elimination               true
% 1.80/0.98  --inst_learning_loop_flag               true
% 1.80/0.98  --inst_learning_start                   3000
% 1.80/0.98  --inst_learning_factor                  2
% 1.80/0.98  --inst_start_prop_sim_after_learn       3
% 1.80/0.98  --inst_sel_renew                        solver
% 1.80/0.98  --inst_lit_activity_flag                true
% 1.80/0.98  --inst_restr_to_given                   false
% 1.80/0.98  --inst_activity_threshold               500
% 1.80/0.98  --inst_out_proof                        true
% 1.80/0.98  
% 1.80/0.98  ------ Resolution Options
% 1.80/0.98  
% 1.80/0.98  --resolution_flag                       true
% 1.80/0.98  --res_lit_sel                           adaptive
% 1.80/0.98  --res_lit_sel_side                      none
% 1.80/0.98  --res_ordering                          kbo
% 1.80/0.98  --res_to_prop_solver                    active
% 1.80/0.98  --res_prop_simpl_new                    false
% 1.80/0.98  --res_prop_simpl_given                  true
% 1.80/0.98  --res_passive_queue_type                priority_queues
% 1.80/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/0.98  --res_passive_queues_freq               [15;5]
% 1.80/0.98  --res_forward_subs                      full
% 1.80/0.98  --res_backward_subs                     full
% 1.80/0.98  --res_forward_subs_resolution           true
% 1.80/0.98  --res_backward_subs_resolution          true
% 1.80/0.98  --res_orphan_elimination                true
% 1.80/0.98  --res_time_limit                        2.
% 1.80/0.98  --res_out_proof                         true
% 1.80/0.98  
% 1.80/0.98  ------ Superposition Options
% 1.80/0.98  
% 1.80/0.98  --superposition_flag                    true
% 1.80/0.98  --sup_passive_queue_type                priority_queues
% 1.80/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.80/0.98  --demod_completeness_check              fast
% 1.80/0.98  --demod_use_ground                      true
% 1.80/0.98  --sup_to_prop_solver                    passive
% 1.80/0.98  --sup_prop_simpl_new                    true
% 1.80/0.98  --sup_prop_simpl_given                  true
% 1.80/0.98  --sup_fun_splitting                     false
% 1.80/0.98  --sup_smt_interval                      50000
% 1.80/0.98  
% 1.80/0.98  ------ Superposition Simplification Setup
% 1.80/0.98  
% 1.80/0.98  --sup_indices_passive                   []
% 1.80/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.98  --sup_full_bw                           [BwDemod]
% 1.80/0.98  --sup_immed_triv                        [TrivRules]
% 1.80/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.98  --sup_immed_bw_main                     []
% 1.80/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.98  
% 1.80/0.98  ------ Combination Options
% 1.80/0.98  
% 1.80/0.98  --comb_res_mult                         3
% 1.80/0.98  --comb_sup_mult                         2
% 1.80/0.98  --comb_inst_mult                        10
% 1.80/0.98  
% 1.80/0.98  ------ Debug Options
% 1.80/0.98  
% 1.80/0.98  --dbg_backtrace                         false
% 1.80/0.98  --dbg_dump_prop_clauses                 false
% 1.80/0.98  --dbg_dump_prop_clauses_file            -
% 1.80/0.98  --dbg_out_stat                          false
% 1.80/0.98  ------ Parsing...
% 1.80/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.80/0.98  
% 1.80/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.80/0.98  
% 1.80/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.80/0.98  
% 1.80/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.80/0.98  ------ Proving...
% 1.80/0.98  ------ Problem Properties 
% 1.80/0.98  
% 1.80/0.98  
% 1.80/0.98  clauses                                 19
% 1.80/0.98  conjectures                             2
% 1.80/0.98  EPR                                     2
% 1.80/0.98  Horn                                    18
% 1.80/0.98  unary                                   7
% 1.80/0.98  binary                                  9
% 1.80/0.98  lits                                    34
% 1.80/0.98  lits eq                                 20
% 1.80/0.98  fd_pure                                 0
% 1.80/0.98  fd_pseudo                               0
% 1.80/0.98  fd_cond                                 2
% 1.80/0.98  fd_pseudo_cond                          1
% 1.80/0.98  AC symbols                              0
% 1.80/0.98  
% 1.80/0.98  ------ Schedule dynamic 5 is on 
% 1.80/0.98  
% 1.80/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.80/0.98  
% 1.80/0.98  
% 1.80/0.98  ------ 
% 1.80/0.98  Current options:
% 1.80/0.98  ------ 
% 1.80/0.98  
% 1.80/0.98  ------ Input Options
% 1.80/0.98  
% 1.80/0.98  --out_options                           all
% 1.80/0.98  --tptp_safe_out                         true
% 1.80/0.98  --problem_path                          ""
% 1.80/0.98  --include_path                          ""
% 1.80/0.98  --clausifier                            res/vclausify_rel
% 1.80/0.98  --clausifier_options                    --mode clausify
% 1.80/0.98  --stdin                                 false
% 1.80/0.98  --stats_out                             all
% 1.80/0.98  
% 1.80/0.98  ------ General Options
% 1.80/0.98  
% 1.80/0.98  --fof                                   false
% 1.80/0.98  --time_out_real                         305.
% 1.80/0.98  --time_out_virtual                      -1.
% 1.80/0.98  --symbol_type_check                     false
% 1.80/0.98  --clausify_out                          false
% 1.80/0.98  --sig_cnt_out                           false
% 1.80/0.98  --trig_cnt_out                          false
% 1.80/0.98  --trig_cnt_out_tolerance                1.
% 1.80/0.98  --trig_cnt_out_sk_spl                   false
% 1.80/0.98  --abstr_cl_out                          false
% 1.80/0.98  
% 1.80/0.98  ------ Global Options
% 1.80/0.98  
% 1.80/0.98  --schedule                              default
% 1.80/0.98  --add_important_lit                     false
% 1.80/0.98  --prop_solver_per_cl                    1000
% 1.80/0.98  --min_unsat_core                        false
% 1.80/0.98  --soft_assumptions                      false
% 1.80/0.98  --soft_lemma_size                       3
% 1.80/0.98  --prop_impl_unit_size                   0
% 1.80/0.98  --prop_impl_unit                        []
% 1.80/0.98  --share_sel_clauses                     true
% 1.80/0.98  --reset_solvers                         false
% 1.80/0.98  --bc_imp_inh                            [conj_cone]
% 1.80/0.98  --conj_cone_tolerance                   3.
% 1.80/0.98  --extra_neg_conj                        none
% 1.80/0.98  --large_theory_mode                     true
% 1.80/0.98  --prolific_symb_bound                   200
% 1.80/0.98  --lt_threshold                          2000
% 1.80/0.98  --clause_weak_htbl                      true
% 1.80/0.98  --gc_record_bc_elim                     false
% 1.80/0.98  
% 1.80/0.98  ------ Preprocessing Options
% 1.80/0.98  
% 1.80/0.98  --preprocessing_flag                    true
% 1.80/0.98  --time_out_prep_mult                    0.1
% 1.80/0.98  --splitting_mode                        input
% 1.80/0.98  --splitting_grd                         true
% 1.80/0.98  --splitting_cvd                         false
% 1.80/0.98  --splitting_cvd_svl                     false
% 1.80/0.98  --splitting_nvd                         32
% 1.80/0.98  --sub_typing                            true
% 1.80/0.98  --prep_gs_sim                           true
% 1.80/0.98  --prep_unflatten                        true
% 1.80/0.98  --prep_res_sim                          true
% 1.80/0.98  --prep_upred                            true
% 1.80/0.98  --prep_sem_filter                       exhaustive
% 1.80/0.98  --prep_sem_filter_out                   false
% 1.80/0.98  --pred_elim                             true
% 1.80/0.98  --res_sim_input                         true
% 1.80/0.98  --eq_ax_congr_red                       true
% 1.80/0.98  --pure_diseq_elim                       true
% 1.80/0.98  --brand_transform                       false
% 1.80/0.98  --non_eq_to_eq                          false
% 1.80/0.98  --prep_def_merge                        true
% 1.80/0.98  --prep_def_merge_prop_impl              false
% 1.80/0.98  --prep_def_merge_mbd                    true
% 1.80/0.98  --prep_def_merge_tr_red                 false
% 1.80/0.98  --prep_def_merge_tr_cl                  false
% 1.80/0.98  --smt_preprocessing                     true
% 1.80/0.98  --smt_ac_axioms                         fast
% 1.80/0.98  --preprocessed_out                      false
% 1.80/0.98  --preprocessed_stats                    false
% 1.80/0.98  
% 1.80/0.98  ------ Abstraction refinement Options
% 1.80/0.98  
% 1.80/0.98  --abstr_ref                             []
% 1.80/0.98  --abstr_ref_prep                        false
% 1.80/0.98  --abstr_ref_until_sat                   false
% 1.80/0.98  --abstr_ref_sig_restrict                funpre
% 1.80/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/0.98  --abstr_ref_under                       []
% 1.80/0.98  
% 1.80/0.98  ------ SAT Options
% 1.80/0.98  
% 1.80/0.98  --sat_mode                              false
% 1.80/0.98  --sat_fm_restart_options                ""
% 1.80/0.99  --sat_gr_def                            false
% 1.80/0.99  --sat_epr_types                         true
% 1.80/0.99  --sat_non_cyclic_types                  false
% 1.80/0.99  --sat_finite_models                     false
% 1.80/0.99  --sat_fm_lemmas                         false
% 1.80/0.99  --sat_fm_prep                           false
% 1.80/0.99  --sat_fm_uc_incr                        true
% 1.80/0.99  --sat_out_model                         small
% 1.80/0.99  --sat_out_clauses                       false
% 1.80/0.99  
% 1.80/0.99  ------ QBF Options
% 1.80/0.99  
% 1.80/0.99  --qbf_mode                              false
% 1.80/0.99  --qbf_elim_univ                         false
% 1.80/0.99  --qbf_dom_inst                          none
% 1.80/0.99  --qbf_dom_pre_inst                      false
% 1.80/0.99  --qbf_sk_in                             false
% 1.80/0.99  --qbf_pred_elim                         true
% 1.80/0.99  --qbf_split                             512
% 1.80/0.99  
% 1.80/0.99  ------ BMC1 Options
% 1.80/0.99  
% 1.80/0.99  --bmc1_incremental                      false
% 1.80/0.99  --bmc1_axioms                           reachable_all
% 1.80/0.99  --bmc1_min_bound                        0
% 1.80/0.99  --bmc1_max_bound                        -1
% 1.80/0.99  --bmc1_max_bound_default                -1
% 1.80/0.99  --bmc1_symbol_reachability              true
% 1.80/0.99  --bmc1_property_lemmas                  false
% 1.80/0.99  --bmc1_k_induction                      false
% 1.80/0.99  --bmc1_non_equiv_states                 false
% 1.80/0.99  --bmc1_deadlock                         false
% 1.80/0.99  --bmc1_ucm                              false
% 1.80/0.99  --bmc1_add_unsat_core                   none
% 1.80/0.99  --bmc1_unsat_core_children              false
% 1.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/0.99  --bmc1_out_stat                         full
% 1.80/0.99  --bmc1_ground_init                      false
% 1.80/0.99  --bmc1_pre_inst_next_state              false
% 1.80/0.99  --bmc1_pre_inst_state                   false
% 1.80/0.99  --bmc1_pre_inst_reach_state             false
% 1.80/0.99  --bmc1_out_unsat_core                   false
% 1.80/0.99  --bmc1_aig_witness_out                  false
% 1.80/0.99  --bmc1_verbose                          false
% 1.80/0.99  --bmc1_dump_clauses_tptp                false
% 1.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.80/0.99  --bmc1_dump_file                        -
% 1.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.80/0.99  --bmc1_ucm_extend_mode                  1
% 1.80/0.99  --bmc1_ucm_init_mode                    2
% 1.80/0.99  --bmc1_ucm_cone_mode                    none
% 1.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.80/0.99  --bmc1_ucm_relax_model                  4
% 1.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/0.99  --bmc1_ucm_layered_model                none
% 1.80/0.99  --bmc1_ucm_max_lemma_size               10
% 1.80/0.99  
% 1.80/0.99  ------ AIG Options
% 1.80/0.99  
% 1.80/0.99  --aig_mode                              false
% 1.80/0.99  
% 1.80/0.99  ------ Instantiation Options
% 1.80/0.99  
% 1.80/0.99  --instantiation_flag                    true
% 1.80/0.99  --inst_sos_flag                         false
% 1.80/0.99  --inst_sos_phase                        true
% 1.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/0.99  --inst_lit_sel_side                     none
% 1.80/0.99  --inst_solver_per_active                1400
% 1.80/0.99  --inst_solver_calls_frac                1.
% 1.80/0.99  --inst_passive_queue_type               priority_queues
% 1.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/0.99  --inst_passive_queues_freq              [25;2]
% 1.80/0.99  --inst_dismatching                      true
% 1.80/0.99  --inst_eager_unprocessed_to_passive     true
% 1.80/0.99  --inst_prop_sim_given                   true
% 1.80/0.99  --inst_prop_sim_new                     false
% 1.80/0.99  --inst_subs_new                         false
% 1.80/0.99  --inst_eq_res_simp                      false
% 1.80/0.99  --inst_subs_given                       false
% 1.80/0.99  --inst_orphan_elimination               true
% 1.80/0.99  --inst_learning_loop_flag               true
% 1.80/0.99  --inst_learning_start                   3000
% 1.80/0.99  --inst_learning_factor                  2
% 1.80/0.99  --inst_start_prop_sim_after_learn       3
% 1.80/0.99  --inst_sel_renew                        solver
% 1.80/0.99  --inst_lit_activity_flag                true
% 1.80/0.99  --inst_restr_to_given                   false
% 1.80/0.99  --inst_activity_threshold               500
% 1.80/0.99  --inst_out_proof                        true
% 1.80/0.99  
% 1.80/0.99  ------ Resolution Options
% 1.80/0.99  
% 1.80/0.99  --resolution_flag                       false
% 1.80/0.99  --res_lit_sel                           adaptive
% 1.80/0.99  --res_lit_sel_side                      none
% 1.80/0.99  --res_ordering                          kbo
% 1.80/0.99  --res_to_prop_solver                    active
% 1.80/0.99  --res_prop_simpl_new                    false
% 1.80/0.99  --res_prop_simpl_given                  true
% 1.80/0.99  --res_passive_queue_type                priority_queues
% 1.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/0.99  --res_passive_queues_freq               [15;5]
% 1.80/0.99  --res_forward_subs                      full
% 1.80/0.99  --res_backward_subs                     full
% 1.80/0.99  --res_forward_subs_resolution           true
% 1.80/0.99  --res_backward_subs_resolution          true
% 1.80/0.99  --res_orphan_elimination                true
% 1.80/0.99  --res_time_limit                        2.
% 1.80/0.99  --res_out_proof                         true
% 1.80/0.99  
% 1.80/0.99  ------ Superposition Options
% 1.80/0.99  
% 1.80/0.99  --superposition_flag                    true
% 1.80/0.99  --sup_passive_queue_type                priority_queues
% 1.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.80/0.99  --demod_completeness_check              fast
% 1.80/0.99  --demod_use_ground                      true
% 1.80/0.99  --sup_to_prop_solver                    passive
% 1.80/0.99  --sup_prop_simpl_new                    true
% 1.80/0.99  --sup_prop_simpl_given                  true
% 1.80/0.99  --sup_fun_splitting                     false
% 1.80/0.99  --sup_smt_interval                      50000
% 1.80/0.99  
% 1.80/0.99  ------ Superposition Simplification Setup
% 1.80/0.99  
% 1.80/0.99  --sup_indices_passive                   []
% 1.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_full_bw                           [BwDemod]
% 1.80/0.99  --sup_immed_triv                        [TrivRules]
% 1.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_immed_bw_main                     []
% 1.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/0.99  
% 1.80/0.99  ------ Combination Options
% 1.80/0.99  
% 1.80/0.99  --comb_res_mult                         3
% 1.80/0.99  --comb_sup_mult                         2
% 1.80/0.99  --comb_inst_mult                        10
% 1.80/0.99  
% 1.80/0.99  ------ Debug Options
% 1.80/0.99  
% 1.80/0.99  --dbg_backtrace                         false
% 1.80/0.99  --dbg_dump_prop_clauses                 false
% 1.80/0.99  --dbg_dump_prop_clauses_file            -
% 1.80/0.99  --dbg_out_stat                          false
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  ------ Proving...
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  % SZS status Theorem for theBenchmark.p
% 1.80/0.99  
% 1.80/0.99   Resolution empty clause
% 1.80/0.99  
% 1.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.80/0.99  
% 1.80/0.99  fof(f15,axiom,(
% 1.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f20,plain,(
% 1.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.80/0.99    inference(pure_predicate_removal,[],[f15])).
% 1.80/0.99  
% 1.80/0.99  fof(f31,plain,(
% 1.80/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.99    inference(ennf_transformation,[],[f20])).
% 1.80/0.99  
% 1.80/0.99  fof(f56,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.80/0.99    inference(cnf_transformation,[],[f31])).
% 1.80/0.99  
% 1.80/0.99  fof(f10,axiom,(
% 1.80/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f24,plain,(
% 1.80/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.80/0.99    inference(ennf_transformation,[],[f10])).
% 1.80/0.99  
% 1.80/0.99  fof(f25,plain,(
% 1.80/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.80/0.99    inference(flattening,[],[f24])).
% 1.80/0.99  
% 1.80/0.99  fof(f49,plain,(
% 1.80/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f25])).
% 1.80/0.99  
% 1.80/0.99  fof(f14,axiom,(
% 1.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f30,plain,(
% 1.80/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.99    inference(ennf_transformation,[],[f14])).
% 1.80/0.99  
% 1.80/0.99  fof(f55,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.80/0.99    inference(cnf_transformation,[],[f30])).
% 1.80/0.99  
% 1.80/0.99  fof(f17,conjecture,(
% 1.80/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f18,negated_conjecture,(
% 1.80/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.80/0.99    inference(negated_conjecture,[],[f17])).
% 1.80/0.99  
% 1.80/0.99  fof(f19,plain,(
% 1.80/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.80/0.99    inference(pure_predicate_removal,[],[f18])).
% 1.80/0.99  
% 1.80/0.99  fof(f33,plain,(
% 1.80/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.80/0.99    inference(ennf_transformation,[],[f19])).
% 1.80/0.99  
% 1.80/0.99  fof(f34,plain,(
% 1.80/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.80/0.99    inference(flattening,[],[f33])).
% 1.80/0.99  
% 1.80/0.99  fof(f37,plain,(
% 1.80/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.80/0.99    introduced(choice_axiom,[])).
% 1.80/0.99  
% 1.80/0.99  fof(f38,plain,(
% 1.80/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f37])).
% 1.80/0.99  
% 1.80/0.99  fof(f59,plain,(
% 1.80/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.80/0.99    inference(cnf_transformation,[],[f38])).
% 1.80/0.99  
% 1.80/0.99  fof(f2,axiom,(
% 1.80/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f40,plain,(
% 1.80/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f2])).
% 1.80/0.99  
% 1.80/0.99  fof(f3,axiom,(
% 1.80/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f41,plain,(
% 1.80/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f3])).
% 1.80/0.99  
% 1.80/0.99  fof(f4,axiom,(
% 1.80/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f42,plain,(
% 1.80/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f4])).
% 1.80/0.99  
% 1.80/0.99  fof(f62,plain,(
% 1.80/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.80/0.99    inference(definition_unfolding,[],[f41,f42])).
% 1.80/0.99  
% 1.80/0.99  fof(f63,plain,(
% 1.80/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.80/0.99    inference(definition_unfolding,[],[f40,f62])).
% 1.80/0.99  
% 1.80/0.99  fof(f69,plain,(
% 1.80/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.80/0.99    inference(definition_unfolding,[],[f59,f63])).
% 1.80/0.99  
% 1.80/0.99  fof(f9,axiom,(
% 1.80/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f23,plain,(
% 1.80/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.80/0.99    inference(ennf_transformation,[],[f9])).
% 1.80/0.99  
% 1.80/0.99  fof(f48,plain,(
% 1.80/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f23])).
% 1.80/0.99  
% 1.80/0.99  fof(f12,axiom,(
% 1.80/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f26,plain,(
% 1.80/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.80/0.99    inference(ennf_transformation,[],[f12])).
% 1.80/0.99  
% 1.80/0.99  fof(f27,plain,(
% 1.80/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.80/0.99    inference(flattening,[],[f26])).
% 1.80/0.99  
% 1.80/0.99  fof(f53,plain,(
% 1.80/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f27])).
% 1.80/0.99  
% 1.80/0.99  fof(f61,plain,(
% 1.80/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.80/0.99    inference(cnf_transformation,[],[f38])).
% 1.80/0.99  
% 1.80/0.99  fof(f68,plain,(
% 1.80/0.99    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.80/0.99    inference(definition_unfolding,[],[f61,f63,f63])).
% 1.80/0.99  
% 1.80/0.99  fof(f16,axiom,(
% 1.80/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f32,plain,(
% 1.80/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.99    inference(ennf_transformation,[],[f16])).
% 1.80/0.99  
% 1.80/0.99  fof(f57,plain,(
% 1.80/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.80/0.99    inference(cnf_transformation,[],[f32])).
% 1.80/0.99  
% 1.80/0.99  fof(f8,axiom,(
% 1.80/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f22,plain,(
% 1.80/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.80/0.99    inference(ennf_transformation,[],[f8])).
% 1.80/0.99  
% 1.80/0.99  fof(f47,plain,(
% 1.80/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f22])).
% 1.80/0.99  
% 1.80/0.99  fof(f13,axiom,(
% 1.80/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f28,plain,(
% 1.80/0.99    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.80/0.99    inference(ennf_transformation,[],[f13])).
% 1.80/0.99  
% 1.80/0.99  fof(f29,plain,(
% 1.80/0.99    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.80/0.99    inference(flattening,[],[f28])).
% 1.80/0.99  
% 1.80/0.99  fof(f54,plain,(
% 1.80/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f29])).
% 1.80/0.99  
% 1.80/0.99  fof(f67,plain,(
% 1.80/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.80/0.99    inference(definition_unfolding,[],[f54,f63,f63])).
% 1.80/0.99  
% 1.80/0.99  fof(f58,plain,(
% 1.80/0.99    v1_funct_1(sK3)),
% 1.80/0.99    inference(cnf_transformation,[],[f38])).
% 1.80/0.99  
% 1.80/0.99  fof(f5,axiom,(
% 1.80/0.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f35,plain,(
% 1.80/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.80/0.99    inference(nnf_transformation,[],[f5])).
% 1.80/0.99  
% 1.80/0.99  fof(f36,plain,(
% 1.80/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.80/0.99    inference(flattening,[],[f35])).
% 1.80/0.99  
% 1.80/0.99  fof(f43,plain,(
% 1.80/0.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.80/0.99    inference(cnf_transformation,[],[f36])).
% 1.80/0.99  
% 1.80/0.99  fof(f66,plain,(
% 1.80/0.99    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.80/0.99    inference(definition_unfolding,[],[f43,f63,f63])).
% 1.80/0.99  
% 1.80/0.99  fof(f6,axiom,(
% 1.80/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f46,plain,(
% 1.80/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.80/0.99    inference(cnf_transformation,[],[f6])).
% 1.80/0.99  
% 1.80/0.99  fof(f11,axiom,(
% 1.80/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f51,plain,(
% 1.80/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.80/0.99    inference(cnf_transformation,[],[f11])).
% 1.80/0.99  
% 1.80/0.99  fof(f1,axiom,(
% 1.80/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/0.99  
% 1.80/0.99  fof(f39,plain,(
% 1.80/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.80/0.99    inference(cnf_transformation,[],[f1])).
% 1.80/0.99  
% 1.80/0.99  cnf(c_14,plain,
% 1.80/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.80/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_7,plain,
% 1.80/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.80/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_218,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/0.99      | ~ v1_relat_1(X0)
% 1.80/0.99      | k7_relat_1(X0,X1) = X0 ),
% 1.80/0.99      inference(resolution,[status(thm)],[c_14,c_7]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_13,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.80/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_222,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/0.99      | k7_relat_1(X0,X1) = X0 ),
% 1.80/0.99      inference(global_propositional_subsumption,
% 1.80/0.99                [status(thm)],
% 1.80/0.99                [c_218,c_14,c_13,c_7]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_18,negated_conjecture,
% 1.80/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 1.80/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_268,plain,
% 1.80/0.99      ( k7_relat_1(X0,X1) = X0
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.80/0.99      | sK3 != X0 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_222,c_18]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_269,plain,
% 1.80/0.99      ( k7_relat_1(sK3,X0) = sK3
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_268]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_814,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 1.80/0.99      | k7_relat_1(sK3,X0_47) = sK3 ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_269]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1191,plain,
% 1.80/0.99      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
% 1.80/0.99      inference(equality_resolution,[status(thm)],[c_814]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_286,plain,
% 1.80/0.99      ( v1_relat_1(X0)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.80/0.99      | sK3 != X0 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_287,plain,
% 1.80/0.99      ( v1_relat_1(sK3)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_286]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_812,plain,
% 1.80/0.99      ( v1_relat_1(sK3)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_287]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1096,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 1.80/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_833,plain,( X0_48 = X0_48 ),theory(equality) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1192,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_833]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1195,plain,
% 1.80/0.99      ( v1_relat_1(sK3)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_812]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1196,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 1.80/0.99      | v1_relat_1(sK3) = iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1195]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1251,plain,
% 1.80/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 1.80/0.99      inference(global_propositional_subsumption,
% 1.80/0.99                [status(thm)],
% 1.80/0.99                [c_1096,c_1192,c_1196]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_6,plain,
% 1.80/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 1.80/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_825,plain,
% 1.80/0.99      ( ~ v1_relat_1(X0_47)
% 1.80/0.99      | k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1090,plain,
% 1.80/0.99      ( k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47)
% 1.80/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1668,plain,
% 1.80/0.99      ( k2_relat_1(k7_relat_1(sK3,X0_47)) = k9_relat_1(sK3,X0_47) ),
% 1.80/0.99      inference(superposition,[status(thm)],[c_1251,c_1090]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1845,plain,
% 1.80/0.99      ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
% 1.80/0.99      inference(superposition,[status(thm)],[c_1191,c_1668]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_10,plain,
% 1.80/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 1.80/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_822,plain,
% 1.80/0.99      ( ~ v1_relat_1(X0_47)
% 1.80/0.99      | k2_relat_1(X0_47) != k1_xboole_0
% 1.80/0.99      | k1_xboole_0 = X0_47 ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1091,plain,
% 1.80/0.99      ( k2_relat_1(X0_47) != k1_xboole_0
% 1.80/0.99      | k1_xboole_0 = X0_47
% 1.80/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1846,plain,
% 1.80/0.99      ( k7_relat_1(sK3,X0_47) = k1_xboole_0
% 1.80/0.99      | k9_relat_1(sK3,X0_47) != k1_xboole_0
% 1.80/0.99      | v1_relat_1(k7_relat_1(sK3,X0_47)) != iProver_top ),
% 1.80/0.99      inference(superposition,[status(thm)],[c_1668,c_1091]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2122,plain,
% 1.80/0.99      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 1.80/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 1.80/0.99      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
% 1.80/0.99      inference(superposition,[status(thm)],[c_1845,c_1846]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2123,plain,
% 1.80/0.99      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 1.80/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 1.80/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.80/0.99      inference(light_normalisation,[status(thm)],[c_2122,c_1191]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2124,plain,
% 1.80/0.99      ( k2_relat_1(sK3) != k1_xboole_0
% 1.80/0.99      | sK3 = k1_xboole_0
% 1.80/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.80/0.99      inference(demodulation,[status(thm)],[c_2123,c_1191]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_16,negated_conjecture,
% 1.80/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 1.80/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_15,plain,
% 1.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.80/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.80/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_277,plain,
% 1.80/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.80/0.99      | sK3 != X2 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_278,plain,
% 1.80/0.99      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_277]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_813,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 1.80/0.99      | k7_relset_1(X0_47,X1_47,sK3,X2_47) = k9_relat_1(sK3,X2_47) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_278]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1193,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 1.80/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_813]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1284,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 1.80/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1193]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_838,plain,
% 1.80/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 1.80/0.99      | r1_tarski(X2_47,X3_47)
% 1.80/0.99      | X2_47 != X0_47
% 1.80/0.99      | X3_47 != X1_47 ),
% 1.80/0.99      theory(equality) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1234,plain,
% 1.80/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 1.80/0.99      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 1.80/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0_47
% 1.80/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1_47 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_838]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1285,plain,
% 1.80/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 1.80/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0_47)
% 1.80/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 1.80/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0_47 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1234]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1338,plain,
% 1.80/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 1.80/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 1.80/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 1.80/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1285]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_5,plain,
% 1.80/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 1.80/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_826,plain,
% 1.80/0.99      ( r1_tarski(k9_relat_1(X0_47,X1_47),k2_relat_1(X0_47))
% 1.80/0.99      | ~ v1_relat_1(X0_47) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1339,plain,
% 1.80/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_826]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_832,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1567,plain,
% 1.80/0.99      ( sK3 = sK3 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_832]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_12,plain,
% 1.80/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
% 1.80/0.99      | ~ v1_funct_1(X0)
% 1.80/0.99      | ~ v1_relat_1(X0) ),
% 1.80/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_19,negated_conjecture,
% 1.80/0.99      ( v1_funct_1(sK3) ),
% 1.80/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_203,plain,
% 1.80/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
% 1.80/0.99      | ~ v1_relat_1(X0)
% 1.80/0.99      | sK3 != X0 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_204,plain,
% 1.80/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)))
% 1.80/0.99      | ~ v1_relat_1(sK3) ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_203]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_818,plain,
% 1.80/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50)))
% 1.80/0.99      | ~ v1_relat_1(sK3) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_204]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1094,plain,
% 1.80/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top
% 1.80/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_880,plain,
% 1.80/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top
% 1.80/0.99      | v1_relat_1(sK3) != iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1387,plain,
% 1.80/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top ),
% 1.80/0.99      inference(global_propositional_subsumption,
% 1.80/0.99                [status(thm)],
% 1.80/0.99                [c_1094,c_880,c_1192,c_1196]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1394,plain,
% 1.80/0.99      ( r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
% 1.80/0.99      inference(superposition,[status(thm)],[c_1191,c_1387]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_3,plain,
% 1.80/0.99      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 1.80/0.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.80/0.99      | k1_xboole_0 = X0 ),
% 1.80/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_827,plain,
% 1.80/0.99      ( ~ r1_tarski(X0_47,k2_enumset1(X0_50,X0_50,X0_50,X0_50))
% 1.80/0.99      | k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_47
% 1.80/0.99      | k1_xboole_0 = X0_47 ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1088,plain,
% 1.80/0.99      ( k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_47
% 1.80/0.99      | k1_xboole_0 = X0_47
% 1.80/0.99      | r1_tarski(X0_47,k2_enumset1(X0_50,X0_50,X0_50,X0_50)) != iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1683,plain,
% 1.80/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 1.80/0.99      | k2_relat_1(sK3) = k1_xboole_0 ),
% 1.80/0.99      inference(superposition,[status(thm)],[c_1394,c_1088]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1802,plain,
% 1.80/0.99      ( ~ v1_relat_1(sK3)
% 1.80/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 1.80/0.99      | k1_xboole_0 = sK3 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_822]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_836,plain,
% 1.80/0.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 1.80/0.99      theory(equality) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1569,plain,
% 1.80/0.99      ( X0_47 != X1_47 | sK3 != X1_47 | sK3 = X0_47 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_836]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1917,plain,
% 1.80/0.99      ( X0_47 != sK3 | sK3 = X0_47 | sK3 != sK3 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1569]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1918,plain,
% 1.80/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_1917]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2127,plain,
% 1.80/0.99      ( sK3 = k1_xboole_0 ),
% 1.80/0.99      inference(global_propositional_subsumption,
% 1.80/0.99                [status(thm)],
% 1.80/0.99                [c_2124,c_16,c_1192,c_1195,c_1284,c_1338,c_1339,c_1567,
% 1.80/0.99                 c_1683,c_1802,c_1918]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1220,plain,
% 1.80/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
% 1.80/0.99      inference(equality_resolution,[status(thm)],[c_813]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_820,negated_conjecture,
% 1.80/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1093,plain,
% 1.80/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1241,plain,
% 1.80/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 1.80/0.99      inference(demodulation,[status(thm)],[c_1220,c_1093]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2137,plain,
% 1.80/0.99      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 1.80/0.99      inference(demodulation,[status(thm)],[c_2127,c_1241]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_4,plain,
% 1.80/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.80/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_256,plain,
% 1.80/0.99      ( v1_relat_1(X0)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 1.80/0.99      | k1_xboole_0 != X0 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_257,plain,
% 1.80/0.99      ( v1_relat_1(k1_xboole_0)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_256]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_815,plain,
% 1.80/0.99      ( v1_relat_1(k1_xboole_0)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_257]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1095,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
% 1.80/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1199,plain,
% 1.80/0.99      ( v1_relat_1(k1_xboole_0)
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_815]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1201,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 1.80/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1199]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1200,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) = k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_833]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1533,plain,
% 1.80/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.80/0.99      inference(global_propositional_subsumption,
% 1.80/0.99                [status(thm)],
% 1.80/0.99                [c_1095,c_1201,c_1200]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1667,plain,
% 1.80/0.99      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0_47)) = k9_relat_1(k1_xboole_0,X0_47) ),
% 1.80/0.99      inference(superposition,[status(thm)],[c_1533,c_1090]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_8,plain,
% 1.80/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.80/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_824,plain,
% 1.80/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_238,plain,
% 1.80/0.99      ( k7_relat_1(X0,X1) = X0
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 1.80/0.99      | k1_xboole_0 != X0 ),
% 1.80/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_222]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_239,plain,
% 1.80/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 1.80/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 1.80/0.99      inference(unflattening,[status(thm)],[c_238]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_817,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
% 1.80/0.99      | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_239]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1312,plain,
% 1.80/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 1.80/0.99      | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 1.80/0.99      inference(instantiation,[status(thm)],[c_817]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1538,plain,
% 1.80/0.99      ( k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 1.80/0.99      inference(global_propositional_subsumption,
% 1.80/0.99                [status(thm)],
% 1.80/0.99                [c_817,c_1200,c_1312]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1672,plain,
% 1.80/0.99      ( k9_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 1.80/0.99      inference(light_normalisation,[status(thm)],[c_1667,c_824,c_1538]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2151,plain,
% 1.80/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 1.80/0.99      inference(demodulation,[status(thm)],[c_2137,c_1672]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_0,plain,
% 1.80/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 1.80/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_830,plain,
% 1.80/0.99      ( r1_tarski(k1_xboole_0,X0_47) ),
% 1.80/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_1085,plain,
% 1.80/0.99      ( r1_tarski(k1_xboole_0,X0_47) = iProver_top ),
% 1.80/0.99      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 1.80/0.99  
% 1.80/0.99  cnf(c_2245,plain,
% 1.80/0.99      ( $false ),
% 1.80/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2151,c_1085]) ).
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.80/0.99  
% 1.80/0.99  ------                               Statistics
% 1.80/0.99  
% 1.80/0.99  ------ General
% 1.80/0.99  
% 1.80/0.99  abstr_ref_over_cycles:                  0
% 1.80/0.99  abstr_ref_under_cycles:                 0
% 1.80/0.99  gc_basic_clause_elim:                   0
% 1.80/0.99  forced_gc_time:                         0
% 1.80/0.99  parsing_time:                           0.009
% 1.80/0.99  unif_index_cands_time:                  0.
% 1.80/0.99  unif_index_add_time:                    0.
% 1.80/0.99  orderings_time:                         0.
% 1.80/0.99  out_proof_time:                         0.012
% 1.80/0.99  total_time:                             0.105
% 1.80/0.99  num_of_symbols:                         54
% 1.80/0.99  num_of_terms:                           2006
% 1.80/0.99  
% 1.80/0.99  ------ Preprocessing
% 1.80/0.99  
% 1.80/0.99  num_of_splits:                          0
% 1.80/0.99  num_of_split_atoms:                     0
% 1.80/0.99  num_of_reused_defs:                     0
% 1.80/0.99  num_eq_ax_congr_red:                    8
% 1.80/0.99  num_of_sem_filtered_clauses:            1
% 1.80/0.99  num_of_subtypes:                        4
% 1.80/0.99  monotx_restored_types:                  0
% 1.80/0.99  sat_num_of_epr_types:                   0
% 1.80/0.99  sat_num_of_non_cyclic_types:            0
% 1.80/0.99  sat_guarded_non_collapsed_types:        1
% 1.80/0.99  num_pure_diseq_elim:                    0
% 1.80/0.99  simp_replaced_by:                       0
% 1.80/0.99  res_preprocessed:                       112
% 1.80/0.99  prep_upred:                             0
% 1.80/0.99  prep_unflattend:                        37
% 1.80/0.99  smt_new_axioms:                         0
% 1.80/0.99  pred_elim_cands:                        2
% 1.80/0.99  pred_elim:                              3
% 1.80/0.99  pred_elim_cl:                           1
% 1.80/0.99  pred_elim_cycles:                       7
% 1.80/0.99  merged_defs:                            0
% 1.80/0.99  merged_defs_ncl:                        0
% 1.80/0.99  bin_hyper_res:                          0
% 1.80/0.99  prep_cycles:                            4
% 1.80/0.99  pred_elim_time:                         0.01
% 1.80/0.99  splitting_time:                         0.
% 1.80/0.99  sem_filter_time:                        0.
% 1.80/0.99  monotx_time:                            0.
% 1.80/0.99  subtype_inf_time:                       0.
% 1.80/0.99  
% 1.80/0.99  ------ Problem properties
% 1.80/0.99  
% 1.80/0.99  clauses:                                19
% 1.80/0.99  conjectures:                            2
% 1.80/0.99  epr:                                    2
% 1.80/0.99  horn:                                   18
% 1.80/0.99  ground:                                 4
% 1.80/0.99  unary:                                  7
% 1.80/0.99  binary:                                 9
% 1.80/0.99  lits:                                   34
% 1.80/0.99  lits_eq:                                20
% 1.80/0.99  fd_pure:                                0
% 1.80/0.99  fd_pseudo:                              0
% 1.80/0.99  fd_cond:                                2
% 1.80/0.99  fd_pseudo_cond:                         1
% 1.80/0.99  ac_symbols:                             0
% 1.80/0.99  
% 1.80/0.99  ------ Propositional Solver
% 1.80/0.99  
% 1.80/0.99  prop_solver_calls:                      28
% 1.80/0.99  prop_fast_solver_calls:                 609
% 1.80/0.99  smt_solver_calls:                       0
% 1.80/0.99  smt_fast_solver_calls:                  0
% 1.80/0.99  prop_num_of_clauses:                    644
% 1.80/0.99  prop_preprocess_simplified:             3128
% 1.80/0.99  prop_fo_subsumed:                       9
% 1.80/0.99  prop_solver_time:                       0.
% 1.80/0.99  smt_solver_time:                        0.
% 1.80/0.99  smt_fast_solver_time:                   0.
% 1.80/0.99  prop_fast_solver_time:                  0.
% 1.80/0.99  prop_unsat_core_time:                   0.
% 1.80/0.99  
% 1.80/0.99  ------ QBF
% 1.80/0.99  
% 1.80/0.99  qbf_q_res:                              0
% 1.80/0.99  qbf_num_tautologies:                    0
% 1.80/0.99  qbf_prep_cycles:                        0
% 1.80/0.99  
% 1.80/0.99  ------ BMC1
% 1.80/0.99  
% 1.80/0.99  bmc1_current_bound:                     -1
% 1.80/0.99  bmc1_last_solved_bound:                 -1
% 1.80/0.99  bmc1_unsat_core_size:                   -1
% 1.80/0.99  bmc1_unsat_core_parents_size:           -1
% 1.80/0.99  bmc1_merge_next_fun:                    0
% 1.80/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.80/0.99  
% 1.80/0.99  ------ Instantiation
% 1.80/0.99  
% 1.80/0.99  inst_num_of_clauses:                    221
% 1.80/0.99  inst_num_in_passive:                    46
% 1.80/0.99  inst_num_in_active:                     161
% 1.80/0.99  inst_num_in_unprocessed:                14
% 1.80/0.99  inst_num_of_loops:                      170
% 1.80/0.99  inst_num_of_learning_restarts:          0
% 1.80/0.99  inst_num_moves_active_passive:          4
% 1.80/0.99  inst_lit_activity:                      0
% 1.80/0.99  inst_lit_activity_moves:                0
% 1.80/0.99  inst_num_tautologies:                   0
% 1.80/0.99  inst_num_prop_implied:                  0
% 1.80/0.99  inst_num_existing_simplified:           0
% 1.80/0.99  inst_num_eq_res_simplified:             0
% 1.80/0.99  inst_num_child_elim:                    0
% 1.80/0.99  inst_num_of_dismatching_blockings:      42
% 1.80/0.99  inst_num_of_non_proper_insts:           214
% 1.80/0.99  inst_num_of_duplicates:                 0
% 1.80/0.99  inst_inst_num_from_inst_to_res:         0
% 1.80/0.99  inst_dismatching_checking_time:         0.
% 1.80/0.99  
% 1.80/0.99  ------ Resolution
% 1.80/0.99  
% 1.80/0.99  res_num_of_clauses:                     0
% 1.80/0.99  res_num_in_passive:                     0
% 1.80/0.99  res_num_in_active:                      0
% 1.80/0.99  res_num_of_loops:                       116
% 1.80/0.99  res_forward_subset_subsumed:            51
% 1.80/0.99  res_backward_subset_subsumed:           0
% 1.80/0.99  res_forward_subsumed:                   0
% 1.80/0.99  res_backward_subsumed:                  0
% 1.80/0.99  res_forward_subsumption_resolution:     0
% 1.80/0.99  res_backward_subsumption_resolution:    0
% 1.80/0.99  res_clause_to_clause_subsumption:       48
% 1.80/0.99  res_orphan_elimination:                 0
% 1.80/0.99  res_tautology_del:                      47
% 1.80/0.99  res_num_eq_res_simplified:              0
% 1.80/0.99  res_num_sel_changes:                    0
% 1.80/0.99  res_moves_from_active_to_pass:          0
% 1.80/0.99  
% 1.80/0.99  ------ Superposition
% 1.80/0.99  
% 1.80/0.99  sup_time_total:                         0.
% 1.80/0.99  sup_time_generating:                    0.
% 1.80/0.99  sup_time_sim_full:                      0.
% 1.80/0.99  sup_time_sim_immed:                     0.
% 1.80/0.99  
% 1.80/0.99  sup_num_of_clauses:                     22
% 1.80/0.99  sup_num_in_active:                      15
% 1.80/0.99  sup_num_in_passive:                     7
% 1.80/0.99  sup_num_of_loops:                       33
% 1.80/0.99  sup_fw_superposition:                   15
% 1.80/0.99  sup_bw_superposition:                   5
% 1.80/0.99  sup_immediate_simplified:               18
% 1.80/0.99  sup_given_eliminated:                   0
% 1.80/0.99  comparisons_done:                       0
% 1.80/0.99  comparisons_avoided:                    0
% 1.80/0.99  
% 1.80/0.99  ------ Simplifications
% 1.80/0.99  
% 1.80/0.99  
% 1.80/0.99  sim_fw_subset_subsumed:                 3
% 1.80/0.99  sim_bw_subset_subsumed:                 0
% 1.80/0.99  sim_fw_subsumed:                        10
% 1.80/0.99  sim_bw_subsumed:                        0
% 1.80/0.99  sim_fw_subsumption_res:                 1
% 1.80/0.99  sim_bw_subsumption_res:                 0
% 1.80/0.99  sim_tautology_del:                      0
% 1.80/0.99  sim_eq_tautology_del:                   4
% 1.80/0.99  sim_eq_res_simp:                        0
% 1.80/0.99  sim_fw_demodulated:                     5
% 1.80/0.99  sim_bw_demodulated:                     18
% 1.80/0.99  sim_light_normalised:                   10
% 1.80/0.99  sim_joinable_taut:                      0
% 1.80/0.99  sim_joinable_simp:                      0
% 1.80/0.99  sim_ac_normalised:                      0
% 1.80/0.99  sim_smt_subsumption:                    0
% 1.80/0.99  
%------------------------------------------------------------------------------
