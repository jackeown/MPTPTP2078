%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:39 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 546 expanded)
%              Number of clauses        :   97 ( 186 expanded)
%              Number of leaves         :   22 ( 122 expanded)
%              Depth                    :   20
%              Number of atoms          :  372 (1331 expanded)
%              Number of equality atoms :  198 ( 568 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f39,plain,
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

fof(f40,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f44,f65,f65])).

fof(f64,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f64,f65,f65])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f65,f65])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_6])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_342,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_15])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_342])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_419,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_343,c_20])).

cnf(c_420,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_850,plain,
    ( r1_tarski(k1_relat_1(sK3),X0_47)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_1189,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | r1_tarski(k1_relat_1(sK3),X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_1519,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1189])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_867,plain,
    ( ~ r1_tarski(X0_47,k1_enumset1(X0_50,X0_50,X0_50))
    | k1_enumset1(X0_50,X0_50,X0_50) = X0_47
    | k1_xboole_0 = X0_47 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1178,plain,
    ( k1_enumset1(X0_50,X0_50,X0_50) = X0_47
    | k1_xboole_0 = X0_47
    | r1_tarski(X0_47,k1_enumset1(X0_50,X0_50,X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_2270,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1519,c_1178])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_224,plain,
    ( ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_225,plain,
    ( ~ v1_relat_1(sK3)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_858,plain,
    ( ~ v1_relat_1(sK3)
    | k1_enumset1(X0_50,X0_50,X0_50) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50)) = k2_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_225])).

cnf(c_921,plain,
    ( ~ v1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_enumset1(sK0,sK0,sK0) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_873,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1303,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_448,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_449,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_854,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_449])).

cnf(c_1307,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_1305,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0))
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_440,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_441,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_855,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k7_relset_1(X0_47,X1_47,sK3,X2_47) = k9_relat_1(sK3,X2_47) ),
    inference(subtyping,[status(esa)],[c_441])).

cnf(c_1304,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_1411,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_878,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_1354,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0_47
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1_47 ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_1412,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0_47)
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1477,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_866,plain,
    ( r1_tarski(k9_relat_1(X0_47,X1_47),k2_relat_1(X0_47))
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1478,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_881,plain,
    ( X0_47 != X1_47
    | k1_relat_1(X0_47) = k1_relat_1(X1_47) ),
    theory(equality)).

cnf(c_1511,plain,
    ( k1_relat_1(sK3) = k1_relat_1(X0_47)
    | sK3 != X0_47 ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_1685,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_872,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1686,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_876,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1509,plain,
    ( X0_47 != X1_47
    | k1_relat_1(sK3) != X1_47
    | k1_relat_1(sK3) = X0_47 ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_1722,plain,
    ( X0_47 != k1_relat_1(sK3)
    | k1_relat_1(sK3) = X0_47
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_1724,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_2040,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_enumset1(X0_50,X0_50,X0_50))
    | k1_enumset1(X0_50,X0_50,X0_50) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_2048,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0))
    | k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_2275,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2270,c_18,c_921,c_1303,c_1307,c_1305,c_1411,c_1477,c_1478,c_1685,c_1686,c_1724,c_2048])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_861,plain,
    ( ~ v1_relat_1(X0_47)
    | k1_relat_1(X0_47) != k1_xboole_0
    | k1_xboole_0 = X0_47 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1182,plain,
    ( k1_relat_1(X0_47) != k1_xboole_0
    | k1_xboole_0 = X0_47
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_2287,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_1182])).

cnf(c_1993,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1687,plain,
    ( X0_47 != X1_47
    | sK3 != X1_47
    | sK3 = X0_47 ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_2121,plain,
    ( X0_47 != sK3
    | sK3 = X0_47
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_2122,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2121])).

cnf(c_2439,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2287,c_18,c_921,c_1303,c_1307,c_1305,c_1411,c_1477,c_1478,c_1685,c_1686,c_1724,c_1993,c_2048,c_2122])).

cnf(c_1334,plain,
    ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
    inference(equality_resolution,[status(thm)],[c_855])).

cnf(c_860,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1183,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_1342,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1334,c_1183])).

cnf(c_2450,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2439,c_1342])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_409,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_410,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_856,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_410])).

cnf(c_1185,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_1313,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_1315,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_1314,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) = k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_1599,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_1315,c_1314])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_865,plain,
    ( ~ v1_relat_1(X0_47)
    | k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1180,plain,
    ( k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47)
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_865])).

cnf(c_1800,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0_47)) = k9_relat_1(k1_xboole_0,X0_47) ),
    inference(superposition,[status(thm)],[c_1599,c_1180])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_864,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_9])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_16,c_15,c_9])).

cnf(c_392,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_325])).

cnf(c_393,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_851,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
    | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_1408,plain,
    ( k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_851])).

cnf(c_1805,plain,
    ( k9_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1800,c_864,c_1408])).

cnf(c_2463,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2450,c_1805])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_870,plain,
    ( r1_tarski(k1_xboole_0,X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1175,plain,
    ( r1_tarski(k1_xboole_0,X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_870])).

cnf(c_2475,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2463,c_1175])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:27:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.06/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/0.98  
% 2.06/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.06/0.98  
% 2.06/0.98  ------  iProver source info
% 2.06/0.98  
% 2.06/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.06/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.06/0.98  git: non_committed_changes: false
% 2.06/0.98  git: last_make_outside_of_git: false
% 2.06/0.98  
% 2.06/0.98  ------ 
% 2.06/0.98  
% 2.06/0.98  ------ Input Options
% 2.06/0.98  
% 2.06/0.98  --out_options                           all
% 2.06/0.98  --tptp_safe_out                         true
% 2.06/0.98  --problem_path                          ""
% 2.06/0.98  --include_path                          ""
% 2.06/0.98  --clausifier                            res/vclausify_rel
% 2.06/0.98  --clausifier_options                    --mode clausify
% 2.06/0.98  --stdin                                 false
% 2.06/0.98  --stats_out                             all
% 2.06/0.98  
% 2.06/0.98  ------ General Options
% 2.06/0.98  
% 2.06/0.98  --fof                                   false
% 2.06/0.98  --time_out_real                         305.
% 2.06/0.98  --time_out_virtual                      -1.
% 2.06/0.98  --symbol_type_check                     false
% 2.06/0.98  --clausify_out                          false
% 2.06/0.98  --sig_cnt_out                           false
% 2.06/0.98  --trig_cnt_out                          false
% 2.06/0.98  --trig_cnt_out_tolerance                1.
% 2.06/0.98  --trig_cnt_out_sk_spl                   false
% 2.06/0.98  --abstr_cl_out                          false
% 2.06/0.98  
% 2.06/0.98  ------ Global Options
% 2.06/0.98  
% 2.06/0.98  --schedule                              default
% 2.06/0.98  --add_important_lit                     false
% 2.06/0.98  --prop_solver_per_cl                    1000
% 2.06/0.98  --min_unsat_core                        false
% 2.06/0.98  --soft_assumptions                      false
% 2.06/0.98  --soft_lemma_size                       3
% 2.06/0.98  --prop_impl_unit_size                   0
% 2.06/0.98  --prop_impl_unit                        []
% 2.06/0.98  --share_sel_clauses                     true
% 2.06/0.98  --reset_solvers                         false
% 2.06/0.98  --bc_imp_inh                            [conj_cone]
% 2.06/0.98  --conj_cone_tolerance                   3.
% 2.06/0.98  --extra_neg_conj                        none
% 2.06/0.98  --large_theory_mode                     true
% 2.06/0.98  --prolific_symb_bound                   200
% 2.06/0.98  --lt_threshold                          2000
% 2.06/0.98  --clause_weak_htbl                      true
% 2.06/0.98  --gc_record_bc_elim                     false
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing Options
% 2.06/0.99  
% 2.06/0.99  --preprocessing_flag                    true
% 2.06/0.99  --time_out_prep_mult                    0.1
% 2.06/0.99  --splitting_mode                        input
% 2.06/0.99  --splitting_grd                         true
% 2.06/0.99  --splitting_cvd                         false
% 2.06/0.99  --splitting_cvd_svl                     false
% 2.06/0.99  --splitting_nvd                         32
% 2.06/0.99  --sub_typing                            true
% 2.06/0.99  --prep_gs_sim                           true
% 2.06/0.99  --prep_unflatten                        true
% 2.06/0.99  --prep_res_sim                          true
% 2.06/0.99  --prep_upred                            true
% 2.06/0.99  --prep_sem_filter                       exhaustive
% 2.06/0.99  --prep_sem_filter_out                   false
% 2.06/0.99  --pred_elim                             true
% 2.06/0.99  --res_sim_input                         true
% 2.06/0.99  --eq_ax_congr_red                       true
% 2.06/0.99  --pure_diseq_elim                       true
% 2.06/0.99  --brand_transform                       false
% 2.06/0.99  --non_eq_to_eq                          false
% 2.06/0.99  --prep_def_merge                        true
% 2.06/0.99  --prep_def_merge_prop_impl              false
% 2.06/0.99  --prep_def_merge_mbd                    true
% 2.06/0.99  --prep_def_merge_tr_red                 false
% 2.06/0.99  --prep_def_merge_tr_cl                  false
% 2.06/0.99  --smt_preprocessing                     true
% 2.06/0.99  --smt_ac_axioms                         fast
% 2.06/0.99  --preprocessed_out                      false
% 2.06/0.99  --preprocessed_stats                    false
% 2.06/0.99  
% 2.06/0.99  ------ Abstraction refinement Options
% 2.06/0.99  
% 2.06/0.99  --abstr_ref                             []
% 2.06/0.99  --abstr_ref_prep                        false
% 2.06/0.99  --abstr_ref_until_sat                   false
% 2.06/0.99  --abstr_ref_sig_restrict                funpre
% 2.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.99  --abstr_ref_under                       []
% 2.06/0.99  
% 2.06/0.99  ------ SAT Options
% 2.06/0.99  
% 2.06/0.99  --sat_mode                              false
% 2.06/0.99  --sat_fm_restart_options                ""
% 2.06/0.99  --sat_gr_def                            false
% 2.06/0.99  --sat_epr_types                         true
% 2.06/0.99  --sat_non_cyclic_types                  false
% 2.06/0.99  --sat_finite_models                     false
% 2.06/0.99  --sat_fm_lemmas                         false
% 2.06/0.99  --sat_fm_prep                           false
% 2.06/0.99  --sat_fm_uc_incr                        true
% 2.06/0.99  --sat_out_model                         small
% 2.06/0.99  --sat_out_clauses                       false
% 2.06/0.99  
% 2.06/0.99  ------ QBF Options
% 2.06/0.99  
% 2.06/0.99  --qbf_mode                              false
% 2.06/0.99  --qbf_elim_univ                         false
% 2.06/0.99  --qbf_dom_inst                          none
% 2.06/0.99  --qbf_dom_pre_inst                      false
% 2.06/0.99  --qbf_sk_in                             false
% 2.06/0.99  --qbf_pred_elim                         true
% 2.06/0.99  --qbf_split                             512
% 2.06/0.99  
% 2.06/0.99  ------ BMC1 Options
% 2.06/0.99  
% 2.06/0.99  --bmc1_incremental                      false
% 2.06/0.99  --bmc1_axioms                           reachable_all
% 2.06/0.99  --bmc1_min_bound                        0
% 2.06/0.99  --bmc1_max_bound                        -1
% 2.06/0.99  --bmc1_max_bound_default                -1
% 2.06/0.99  --bmc1_symbol_reachability              true
% 2.06/0.99  --bmc1_property_lemmas                  false
% 2.06/0.99  --bmc1_k_induction                      false
% 2.06/0.99  --bmc1_non_equiv_states                 false
% 2.06/0.99  --bmc1_deadlock                         false
% 2.06/0.99  --bmc1_ucm                              false
% 2.06/0.99  --bmc1_add_unsat_core                   none
% 2.06/0.99  --bmc1_unsat_core_children              false
% 2.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.99  --bmc1_out_stat                         full
% 2.06/0.99  --bmc1_ground_init                      false
% 2.06/0.99  --bmc1_pre_inst_next_state              false
% 2.06/0.99  --bmc1_pre_inst_state                   false
% 2.06/0.99  --bmc1_pre_inst_reach_state             false
% 2.06/0.99  --bmc1_out_unsat_core                   false
% 2.06/0.99  --bmc1_aig_witness_out                  false
% 2.06/0.99  --bmc1_verbose                          false
% 2.06/0.99  --bmc1_dump_clauses_tptp                false
% 2.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.99  --bmc1_dump_file                        -
% 2.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.99  --bmc1_ucm_extend_mode                  1
% 2.06/0.99  --bmc1_ucm_init_mode                    2
% 2.06/0.99  --bmc1_ucm_cone_mode                    none
% 2.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.99  --bmc1_ucm_relax_model                  4
% 2.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.99  --bmc1_ucm_layered_model                none
% 2.06/0.99  --bmc1_ucm_max_lemma_size               10
% 2.06/0.99  
% 2.06/0.99  ------ AIG Options
% 2.06/0.99  
% 2.06/0.99  --aig_mode                              false
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation Options
% 2.06/0.99  
% 2.06/0.99  --instantiation_flag                    true
% 2.06/0.99  --inst_sos_flag                         false
% 2.06/0.99  --inst_sos_phase                        true
% 2.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel_side                     num_symb
% 2.06/0.99  --inst_solver_per_active                1400
% 2.06/0.99  --inst_solver_calls_frac                1.
% 2.06/0.99  --inst_passive_queue_type               priority_queues
% 2.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.99  --inst_passive_queues_freq              [25;2]
% 2.06/0.99  --inst_dismatching                      true
% 2.06/0.99  --inst_eager_unprocessed_to_passive     true
% 2.06/0.99  --inst_prop_sim_given                   true
% 2.06/0.99  --inst_prop_sim_new                     false
% 2.06/0.99  --inst_subs_new                         false
% 2.06/0.99  --inst_eq_res_simp                      false
% 2.06/0.99  --inst_subs_given                       false
% 2.06/0.99  --inst_orphan_elimination               true
% 2.06/0.99  --inst_learning_loop_flag               true
% 2.06/0.99  --inst_learning_start                   3000
% 2.06/0.99  --inst_learning_factor                  2
% 2.06/0.99  --inst_start_prop_sim_after_learn       3
% 2.06/0.99  --inst_sel_renew                        solver
% 2.06/0.99  --inst_lit_activity_flag                true
% 2.06/0.99  --inst_restr_to_given                   false
% 2.06/0.99  --inst_activity_threshold               500
% 2.06/0.99  --inst_out_proof                        true
% 2.06/0.99  
% 2.06/0.99  ------ Resolution Options
% 2.06/0.99  
% 2.06/0.99  --resolution_flag                       true
% 2.06/0.99  --res_lit_sel                           adaptive
% 2.06/0.99  --res_lit_sel_side                      none
% 2.06/0.99  --res_ordering                          kbo
% 2.06/0.99  --res_to_prop_solver                    active
% 2.06/0.99  --res_prop_simpl_new                    false
% 2.06/0.99  --res_prop_simpl_given                  true
% 2.06/0.99  --res_passive_queue_type                priority_queues
% 2.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.99  --res_passive_queues_freq               [15;5]
% 2.06/0.99  --res_forward_subs                      full
% 2.06/0.99  --res_backward_subs                     full
% 2.06/0.99  --res_forward_subs_resolution           true
% 2.06/0.99  --res_backward_subs_resolution          true
% 2.06/0.99  --res_orphan_elimination                true
% 2.06/0.99  --res_time_limit                        2.
% 2.06/0.99  --res_out_proof                         true
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Options
% 2.06/0.99  
% 2.06/0.99  --superposition_flag                    true
% 2.06/0.99  --sup_passive_queue_type                priority_queues
% 2.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.99  --demod_completeness_check              fast
% 2.06/0.99  --demod_use_ground                      true
% 2.06/0.99  --sup_to_prop_solver                    passive
% 2.06/0.99  --sup_prop_simpl_new                    true
% 2.06/0.99  --sup_prop_simpl_given                  true
% 2.06/0.99  --sup_fun_splitting                     false
% 2.06/0.99  --sup_smt_interval                      50000
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Simplification Setup
% 2.06/0.99  
% 2.06/0.99  --sup_indices_passive                   []
% 2.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_full_bw                           [BwDemod]
% 2.06/0.99  --sup_immed_triv                        [TrivRules]
% 2.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_immed_bw_main                     []
% 2.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  
% 2.06/0.99  ------ Combination Options
% 2.06/0.99  
% 2.06/0.99  --comb_res_mult                         3
% 2.06/0.99  --comb_sup_mult                         2
% 2.06/0.99  --comb_inst_mult                        10
% 2.06/0.99  
% 2.06/0.99  ------ Debug Options
% 2.06/0.99  
% 2.06/0.99  --dbg_backtrace                         false
% 2.06/0.99  --dbg_dump_prop_clauses                 false
% 2.06/0.99  --dbg_dump_prop_clauses_file            -
% 2.06/0.99  --dbg_out_stat                          false
% 2.06/0.99  ------ Parsing...
% 2.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.06/0.99  ------ Proving...
% 2.06/0.99  ------ Problem Properties 
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  clauses                                 22
% 2.06/0.99  conjectures                             2
% 2.06/0.99  EPR                                     2
% 2.06/0.99  Horn                                    21
% 2.06/0.99  unary                                   7
% 2.06/0.99  binary                                  10
% 2.06/0.99  lits                                    42
% 2.06/0.99  lits eq                                 25
% 2.06/0.99  fd_pure                                 0
% 2.06/0.99  fd_pseudo                               0
% 2.06/0.99  fd_cond                                 2
% 2.06/0.99  fd_pseudo_cond                          1
% 2.06/0.99  AC symbols                              0
% 2.06/0.99  
% 2.06/0.99  ------ Schedule dynamic 5 is on 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  ------ 
% 2.06/0.99  Current options:
% 2.06/0.99  ------ 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options
% 2.06/0.99  
% 2.06/0.99  --out_options                           all
% 2.06/0.99  --tptp_safe_out                         true
% 2.06/0.99  --problem_path                          ""
% 2.06/0.99  --include_path                          ""
% 2.06/0.99  --clausifier                            res/vclausify_rel
% 2.06/0.99  --clausifier_options                    --mode clausify
% 2.06/0.99  --stdin                                 false
% 2.06/0.99  --stats_out                             all
% 2.06/0.99  
% 2.06/0.99  ------ General Options
% 2.06/0.99  
% 2.06/0.99  --fof                                   false
% 2.06/0.99  --time_out_real                         305.
% 2.06/0.99  --time_out_virtual                      -1.
% 2.06/0.99  --symbol_type_check                     false
% 2.06/0.99  --clausify_out                          false
% 2.06/0.99  --sig_cnt_out                           false
% 2.06/0.99  --trig_cnt_out                          false
% 2.06/0.99  --trig_cnt_out_tolerance                1.
% 2.06/0.99  --trig_cnt_out_sk_spl                   false
% 2.06/0.99  --abstr_cl_out                          false
% 2.06/0.99  
% 2.06/0.99  ------ Global Options
% 2.06/0.99  
% 2.06/0.99  --schedule                              default
% 2.06/0.99  --add_important_lit                     false
% 2.06/0.99  --prop_solver_per_cl                    1000
% 2.06/0.99  --min_unsat_core                        false
% 2.06/0.99  --soft_assumptions                      false
% 2.06/0.99  --soft_lemma_size                       3
% 2.06/0.99  --prop_impl_unit_size                   0
% 2.06/0.99  --prop_impl_unit                        []
% 2.06/0.99  --share_sel_clauses                     true
% 2.06/0.99  --reset_solvers                         false
% 2.06/0.99  --bc_imp_inh                            [conj_cone]
% 2.06/0.99  --conj_cone_tolerance                   3.
% 2.06/0.99  --extra_neg_conj                        none
% 2.06/0.99  --large_theory_mode                     true
% 2.06/0.99  --prolific_symb_bound                   200
% 2.06/0.99  --lt_threshold                          2000
% 2.06/0.99  --clause_weak_htbl                      true
% 2.06/0.99  --gc_record_bc_elim                     false
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing Options
% 2.06/0.99  
% 2.06/0.99  --preprocessing_flag                    true
% 2.06/0.99  --time_out_prep_mult                    0.1
% 2.06/0.99  --splitting_mode                        input
% 2.06/0.99  --splitting_grd                         true
% 2.06/0.99  --splitting_cvd                         false
% 2.06/0.99  --splitting_cvd_svl                     false
% 2.06/0.99  --splitting_nvd                         32
% 2.06/0.99  --sub_typing                            true
% 2.06/0.99  --prep_gs_sim                           true
% 2.06/0.99  --prep_unflatten                        true
% 2.06/0.99  --prep_res_sim                          true
% 2.06/0.99  --prep_upred                            true
% 2.06/0.99  --prep_sem_filter                       exhaustive
% 2.06/0.99  --prep_sem_filter_out                   false
% 2.06/0.99  --pred_elim                             true
% 2.06/0.99  --res_sim_input                         true
% 2.06/0.99  --eq_ax_congr_red                       true
% 2.06/0.99  --pure_diseq_elim                       true
% 2.06/0.99  --brand_transform                       false
% 2.06/0.99  --non_eq_to_eq                          false
% 2.06/0.99  --prep_def_merge                        true
% 2.06/0.99  --prep_def_merge_prop_impl              false
% 2.06/0.99  --prep_def_merge_mbd                    true
% 2.06/0.99  --prep_def_merge_tr_red                 false
% 2.06/0.99  --prep_def_merge_tr_cl                  false
% 2.06/0.99  --smt_preprocessing                     true
% 2.06/0.99  --smt_ac_axioms                         fast
% 2.06/0.99  --preprocessed_out                      false
% 2.06/0.99  --preprocessed_stats                    false
% 2.06/0.99  
% 2.06/0.99  ------ Abstraction refinement Options
% 2.06/0.99  
% 2.06/0.99  --abstr_ref                             []
% 2.06/0.99  --abstr_ref_prep                        false
% 2.06/0.99  --abstr_ref_until_sat                   false
% 2.06/0.99  --abstr_ref_sig_restrict                funpre
% 2.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.99  --abstr_ref_under                       []
% 2.06/0.99  
% 2.06/0.99  ------ SAT Options
% 2.06/0.99  
% 2.06/0.99  --sat_mode                              false
% 2.06/0.99  --sat_fm_restart_options                ""
% 2.06/0.99  --sat_gr_def                            false
% 2.06/0.99  --sat_epr_types                         true
% 2.06/0.99  --sat_non_cyclic_types                  false
% 2.06/0.99  --sat_finite_models                     false
% 2.06/0.99  --sat_fm_lemmas                         false
% 2.06/0.99  --sat_fm_prep                           false
% 2.06/0.99  --sat_fm_uc_incr                        true
% 2.06/0.99  --sat_out_model                         small
% 2.06/0.99  --sat_out_clauses                       false
% 2.06/0.99  
% 2.06/0.99  ------ QBF Options
% 2.06/0.99  
% 2.06/0.99  --qbf_mode                              false
% 2.06/0.99  --qbf_elim_univ                         false
% 2.06/0.99  --qbf_dom_inst                          none
% 2.06/0.99  --qbf_dom_pre_inst                      false
% 2.06/0.99  --qbf_sk_in                             false
% 2.06/0.99  --qbf_pred_elim                         true
% 2.06/0.99  --qbf_split                             512
% 2.06/0.99  
% 2.06/0.99  ------ BMC1 Options
% 2.06/0.99  
% 2.06/0.99  --bmc1_incremental                      false
% 2.06/0.99  --bmc1_axioms                           reachable_all
% 2.06/0.99  --bmc1_min_bound                        0
% 2.06/0.99  --bmc1_max_bound                        -1
% 2.06/0.99  --bmc1_max_bound_default                -1
% 2.06/0.99  --bmc1_symbol_reachability              true
% 2.06/0.99  --bmc1_property_lemmas                  false
% 2.06/0.99  --bmc1_k_induction                      false
% 2.06/0.99  --bmc1_non_equiv_states                 false
% 2.06/0.99  --bmc1_deadlock                         false
% 2.06/0.99  --bmc1_ucm                              false
% 2.06/0.99  --bmc1_add_unsat_core                   none
% 2.06/0.99  --bmc1_unsat_core_children              false
% 2.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.99  --bmc1_out_stat                         full
% 2.06/0.99  --bmc1_ground_init                      false
% 2.06/0.99  --bmc1_pre_inst_next_state              false
% 2.06/0.99  --bmc1_pre_inst_state                   false
% 2.06/0.99  --bmc1_pre_inst_reach_state             false
% 2.06/0.99  --bmc1_out_unsat_core                   false
% 2.06/0.99  --bmc1_aig_witness_out                  false
% 2.06/0.99  --bmc1_verbose                          false
% 2.06/0.99  --bmc1_dump_clauses_tptp                false
% 2.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.99  --bmc1_dump_file                        -
% 2.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.99  --bmc1_ucm_extend_mode                  1
% 2.06/0.99  --bmc1_ucm_init_mode                    2
% 2.06/0.99  --bmc1_ucm_cone_mode                    none
% 2.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.99  --bmc1_ucm_relax_model                  4
% 2.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.99  --bmc1_ucm_layered_model                none
% 2.06/0.99  --bmc1_ucm_max_lemma_size               10
% 2.06/0.99  
% 2.06/0.99  ------ AIG Options
% 2.06/0.99  
% 2.06/0.99  --aig_mode                              false
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation Options
% 2.06/0.99  
% 2.06/0.99  --instantiation_flag                    true
% 2.06/0.99  --inst_sos_flag                         false
% 2.06/0.99  --inst_sos_phase                        true
% 2.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel_side                     none
% 2.06/0.99  --inst_solver_per_active                1400
% 2.06/0.99  --inst_solver_calls_frac                1.
% 2.06/0.99  --inst_passive_queue_type               priority_queues
% 2.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.99  --inst_passive_queues_freq              [25;2]
% 2.06/0.99  --inst_dismatching                      true
% 2.06/0.99  --inst_eager_unprocessed_to_passive     true
% 2.06/0.99  --inst_prop_sim_given                   true
% 2.06/0.99  --inst_prop_sim_new                     false
% 2.06/0.99  --inst_subs_new                         false
% 2.06/0.99  --inst_eq_res_simp                      false
% 2.06/0.99  --inst_subs_given                       false
% 2.06/0.99  --inst_orphan_elimination               true
% 2.06/0.99  --inst_learning_loop_flag               true
% 2.06/0.99  --inst_learning_start                   3000
% 2.06/0.99  --inst_learning_factor                  2
% 2.06/0.99  --inst_start_prop_sim_after_learn       3
% 2.06/0.99  --inst_sel_renew                        solver
% 2.06/0.99  --inst_lit_activity_flag                true
% 2.06/0.99  --inst_restr_to_given                   false
% 2.06/0.99  --inst_activity_threshold               500
% 2.06/0.99  --inst_out_proof                        true
% 2.06/0.99  
% 2.06/0.99  ------ Resolution Options
% 2.06/0.99  
% 2.06/0.99  --resolution_flag                       false
% 2.06/0.99  --res_lit_sel                           adaptive
% 2.06/0.99  --res_lit_sel_side                      none
% 2.06/0.99  --res_ordering                          kbo
% 2.06/0.99  --res_to_prop_solver                    active
% 2.06/0.99  --res_prop_simpl_new                    false
% 2.06/0.99  --res_prop_simpl_given                  true
% 2.06/0.99  --res_passive_queue_type                priority_queues
% 2.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.99  --res_passive_queues_freq               [15;5]
% 2.06/0.99  --res_forward_subs                      full
% 2.06/0.99  --res_backward_subs                     full
% 2.06/0.99  --res_forward_subs_resolution           true
% 2.06/0.99  --res_backward_subs_resolution          true
% 2.06/0.99  --res_orphan_elimination                true
% 2.06/0.99  --res_time_limit                        2.
% 2.06/0.99  --res_out_proof                         true
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Options
% 2.06/0.99  
% 2.06/0.99  --superposition_flag                    true
% 2.06/0.99  --sup_passive_queue_type                priority_queues
% 2.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.99  --demod_completeness_check              fast
% 2.06/0.99  --demod_use_ground                      true
% 2.06/0.99  --sup_to_prop_solver                    passive
% 2.06/0.99  --sup_prop_simpl_new                    true
% 2.06/0.99  --sup_prop_simpl_given                  true
% 2.06/0.99  --sup_fun_splitting                     false
% 2.06/0.99  --sup_smt_interval                      50000
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Simplification Setup
% 2.06/0.99  
% 2.06/0.99  --sup_indices_passive                   []
% 2.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_full_bw                           [BwDemod]
% 2.06/0.99  --sup_immed_triv                        [TrivRules]
% 2.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_immed_bw_main                     []
% 2.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  
% 2.06/0.99  ------ Combination Options
% 2.06/0.99  
% 2.06/0.99  --comb_res_mult                         3
% 2.06/0.99  --comb_sup_mult                         2
% 2.06/0.99  --comb_inst_mult                        10
% 2.06/0.99  
% 2.06/0.99  ------ Debug Options
% 2.06/0.99  
% 2.06/0.99  --dbg_backtrace                         false
% 2.06/0.99  --dbg_dump_prop_clauses                 false
% 2.06/0.99  --dbg_dump_prop_clauses_file            -
% 2.06/0.99  --dbg_out_stat                          false
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  ------ Proving...
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  % SZS status Theorem for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99   Resolution empty clause
% 2.06/0.99  
% 2.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  fof(f15,axiom,(
% 2.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f20,plain,(
% 2.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.06/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.06/0.99  
% 2.06/0.99  fof(f32,plain,(
% 2.06/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.99    inference(ennf_transformation,[],[f20])).
% 2.06/0.99  
% 2.06/0.99  fof(f59,plain,(
% 2.06/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f32])).
% 2.06/0.99  
% 2.06/0.99  fof(f7,axiom,(
% 2.06/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f22,plain,(
% 2.06/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.06/0.99    inference(ennf_transformation,[],[f7])).
% 2.06/0.99  
% 2.06/0.99  fof(f38,plain,(
% 2.06/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.06/0.99    inference(nnf_transformation,[],[f22])).
% 2.06/0.99  
% 2.06/0.99  fof(f48,plain,(
% 2.06/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f38])).
% 2.06/0.99  
% 2.06/0.99  fof(f14,axiom,(
% 2.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f31,plain,(
% 2.06/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.99    inference(ennf_transformation,[],[f14])).
% 2.06/0.99  
% 2.06/0.99  fof(f58,plain,(
% 2.06/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f31])).
% 2.06/0.99  
% 2.06/0.99  fof(f17,conjecture,(
% 2.06/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f18,negated_conjecture,(
% 2.06/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.06/0.99    inference(negated_conjecture,[],[f17])).
% 2.06/0.99  
% 2.06/0.99  fof(f19,plain,(
% 2.06/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.06/0.99    inference(pure_predicate_removal,[],[f18])).
% 2.06/0.99  
% 2.06/0.99  fof(f34,plain,(
% 2.06/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.06/0.99    inference(ennf_transformation,[],[f19])).
% 2.06/0.99  
% 2.06/0.99  fof(f35,plain,(
% 2.06/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.06/0.99    inference(flattening,[],[f34])).
% 2.06/0.99  
% 2.06/0.99  fof(f39,plain,(
% 2.06/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f40,plain,(
% 2.06/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39])).
% 2.06/0.99  
% 2.06/0.99  fof(f62,plain,(
% 2.06/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.06/0.99    inference(cnf_transformation,[],[f40])).
% 2.06/0.99  
% 2.06/0.99  fof(f2,axiom,(
% 2.06/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f42,plain,(
% 2.06/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f2])).
% 2.06/0.99  
% 2.06/0.99  fof(f3,axiom,(
% 2.06/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f43,plain,(
% 2.06/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f3])).
% 2.06/0.99  
% 2.06/0.99  fof(f65,plain,(
% 2.06/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.06/0.99    inference(definition_unfolding,[],[f42,f43])).
% 2.06/0.99  
% 2.06/0.99  fof(f71,plain,(
% 2.06/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 2.06/0.99    inference(definition_unfolding,[],[f62,f65])).
% 2.06/0.99  
% 2.06/0.99  fof(f4,axiom,(
% 2.06/0.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f36,plain,(
% 2.06/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.06/0.99    inference(nnf_transformation,[],[f4])).
% 2.06/0.99  
% 2.06/0.99  fof(f37,plain,(
% 2.06/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.06/0.99    inference(flattening,[],[f36])).
% 2.06/0.99  
% 2.06/0.99  fof(f44,plain,(
% 2.06/0.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f37])).
% 2.06/0.99  
% 2.06/0.99  fof(f68,plain,(
% 2.06/0.99    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 2.06/0.99    inference(definition_unfolding,[],[f44,f65,f65])).
% 2.06/0.99  
% 2.06/0.99  fof(f64,plain,(
% 2.06/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.06/0.99    inference(cnf_transformation,[],[f40])).
% 2.06/0.99  
% 2.06/0.99  fof(f70,plain,(
% 2.06/0.99    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.06/0.99    inference(definition_unfolding,[],[f64,f65,f65])).
% 2.06/0.99  
% 2.06/0.99  fof(f13,axiom,(
% 2.06/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f29,plain,(
% 2.06/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.06/0.99    inference(ennf_transformation,[],[f13])).
% 2.06/0.99  
% 2.06/0.99  fof(f30,plain,(
% 2.06/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.06/0.99    inference(flattening,[],[f29])).
% 2.06/0.99  
% 2.06/0.99  fof(f57,plain,(
% 2.06/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f30])).
% 2.06/0.99  
% 2.06/0.99  fof(f69,plain,(
% 2.06/0.99    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_enumset1(X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.06/0.99    inference(definition_unfolding,[],[f57,f65,f65])).
% 2.06/0.99  
% 2.06/0.99  fof(f61,plain,(
% 2.06/0.99    v1_funct_1(sK3)),
% 2.06/0.99    inference(cnf_transformation,[],[f40])).
% 2.06/0.99  
% 2.06/0.99  fof(f16,axiom,(
% 2.06/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f33,plain,(
% 2.06/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.99    inference(ennf_transformation,[],[f16])).
% 2.06/0.99  
% 2.06/0.99  fof(f60,plain,(
% 2.06/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f33])).
% 2.06/0.99  
% 2.06/0.99  fof(f8,axiom,(
% 2.06/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f23,plain,(
% 2.06/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.06/0.99    inference(ennf_transformation,[],[f8])).
% 2.06/0.99  
% 2.06/0.99  fof(f50,plain,(
% 2.06/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f23])).
% 2.06/0.99  
% 2.06/0.99  fof(f12,axiom,(
% 2.06/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f27,plain,(
% 2.06/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f12])).
% 2.06/0.99  
% 2.06/0.99  fof(f28,plain,(
% 2.06/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.06/0.99    inference(flattening,[],[f27])).
% 2.06/0.99  
% 2.06/0.99  fof(f55,plain,(
% 2.06/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f28])).
% 2.06/0.99  
% 2.06/0.99  fof(f5,axiom,(
% 2.06/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f47,plain,(
% 2.06/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f5])).
% 2.06/0.99  
% 2.06/0.99  fof(f9,axiom,(
% 2.06/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f24,plain,(
% 2.06/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.06/0.99    inference(ennf_transformation,[],[f9])).
% 2.06/0.99  
% 2.06/0.99  fof(f51,plain,(
% 2.06/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f24])).
% 2.06/0.99  
% 2.06/0.99  fof(f11,axiom,(
% 2.06/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f54,plain,(
% 2.06/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.06/0.99    inference(cnf_transformation,[],[f11])).
% 2.06/0.99  
% 2.06/0.99  fof(f10,axiom,(
% 2.06/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f25,plain,(
% 2.06/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.06/0.99    inference(ennf_transformation,[],[f10])).
% 2.06/0.99  
% 2.06/0.99  fof(f26,plain,(
% 2.06/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.06/0.99    inference(flattening,[],[f25])).
% 2.06/0.99  
% 2.06/0.99  fof(f52,plain,(
% 2.06/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f26])).
% 2.06/0.99  
% 2.06/0.99  fof(f1,axiom,(
% 2.06/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f41,plain,(
% 2.06/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f1])).
% 2.06/0.99  
% 2.06/0.99  cnf(c_16,plain,
% 2.06/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.06/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6,plain,
% 2.06/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_338,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.06/0.99      | ~ v1_relat_1(X0) ),
% 2.06/0.99      inference(resolution,[status(thm)],[c_16,c_6]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_15,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_342,plain,
% 2.06/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.06/0.99      inference(global_propositional_subsumption,[status(thm)],[c_338,c_15]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_343,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_342]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_20,negated_conjecture,
% 2.06/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
% 2.06/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_419,plain,
% 2.06/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.06/0.99      | sK3 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_343,c_20]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_420,plain,
% 2.06/0.99      ( r1_tarski(k1_relat_1(sK3),X0)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_419]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_850,plain,
% 2.06/0.99      ( r1_tarski(k1_relat_1(sK3),X0_47)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_420]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1189,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 2.06/0.99      | r1_tarski(k1_relat_1(sK3),X0_47) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1519,plain,
% 2.06/0.99      ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
% 2.06/0.99      inference(equality_resolution,[status(thm)],[c_1189]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3,plain,
% 2.06/0.99      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
% 2.06/0.99      | k1_enumset1(X1,X1,X1) = X0
% 2.06/0.99      | k1_xboole_0 = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_867,plain,
% 2.06/0.99      ( ~ r1_tarski(X0_47,k1_enumset1(X0_50,X0_50,X0_50))
% 2.06/0.99      | k1_enumset1(X0_50,X0_50,X0_50) = X0_47
% 2.06/0.99      | k1_xboole_0 = X0_47 ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1178,plain,
% 2.06/0.99      ( k1_enumset1(X0_50,X0_50,X0_50) = X0_47
% 2.06/0.99      | k1_xboole_0 = X0_47
% 2.06/0.99      | r1_tarski(X0_47,k1_enumset1(X0_50,X0_50,X0_50)) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_867]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2270,plain,
% 2.06/0.99      ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.06/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_1519,c_1178]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_18,negated_conjecture,
% 2.06/0.99      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.06/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_14,plain,
% 2.06/0.99      ( ~ v1_funct_1(X0)
% 2.06/0.99      | ~ v1_relat_1(X0)
% 2.06/0.99      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 2.06/0.99      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_21,negated_conjecture,
% 2.06/0.99      ( v1_funct_1(sK3) ),
% 2.06/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_224,plain,
% 2.06/0.99      ( ~ v1_relat_1(X0)
% 2.06/0.99      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 2.06/0.99      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.06/0.99      | sK3 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_225,plain,
% 2.06/0.99      ( ~ v1_relat_1(sK3)
% 2.06/0.99      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 2.06/0.99      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_224]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_858,plain,
% 2.06/0.99      ( ~ v1_relat_1(sK3)
% 2.06/0.99      | k1_enumset1(X0_50,X0_50,X0_50) != k1_relat_1(sK3)
% 2.06/0.99      | k1_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50)) = k2_relat_1(sK3) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_225]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_921,plain,
% 2.06/0.99      ( ~ v1_relat_1(sK3)
% 2.06/0.99      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.06/0.99      | k1_enumset1(sK0,sK0,sK0) != k1_relat_1(sK3) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_858]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_873,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1303,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_873]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_448,plain,
% 2.06/0.99      ( v1_relat_1(X0)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.06/0.99      | sK3 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_449,plain,
% 2.06/0.99      ( v1_relat_1(sK3)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_448]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_854,plain,
% 2.06/0.99      ( v1_relat_1(sK3)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_449]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1307,plain,
% 2.06/0.99      ( v1_relat_1(sK3)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_854]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1305,plain,
% 2.06/0.99      ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0))
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_850]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_17,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.06/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_440,plain,
% 2.06/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.06/0.99      | sK3 != X2 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_441,plain,
% 2.06/0.99      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_855,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 2.06/0.99      | k7_relset_1(X0_47,X1_47,sK3,X2_47) = k9_relat_1(sK3,X2_47) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_441]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1304,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
% 2.06/0.99      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_855]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1411,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))
% 2.06/0.99      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_878,plain,
% 2.06/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 2.06/0.99      | r1_tarski(X2_47,X3_47)
% 2.06/0.99      | X2_47 != X0_47
% 2.06/0.99      | X3_47 != X1_47 ),
% 2.06/0.99      theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1354,plain,
% 2.06/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 2.06/0.99      | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.06/0.99      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0_47
% 2.06/0.99      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1_47 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_878]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1412,plain,
% 2.06/0.99      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.06/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0_47)
% 2.06/0.99      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.06/0.99      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0_47 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1477,plain,
% 2.06/0.99      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.06/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.06/0.99      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.06/0.99      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1412]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7,plain,
% 2.06/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_866,plain,
% 2.06/0.99      ( r1_tarski(k9_relat_1(X0_47,X1_47),k2_relat_1(X0_47))
% 2.06/0.99      | ~ v1_relat_1(X0_47) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1478,plain,
% 2.06/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_866]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_881,plain,
% 2.06/0.99      ( X0_47 != X1_47 | k1_relat_1(X0_47) = k1_relat_1(X1_47) ),
% 2.06/0.99      theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1511,plain,
% 2.06/0.99      ( k1_relat_1(sK3) = k1_relat_1(X0_47) | sK3 != X0_47 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_881]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1685,plain,
% 2.06/0.99      ( k1_relat_1(sK3) = k1_relat_1(sK3) | sK3 != sK3 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1511]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_872,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1686,plain,
% 2.06/0.99      ( sK3 = sK3 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_872]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_876,plain,
% 2.06/0.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.06/0.99      theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1509,plain,
% 2.06/0.99      ( X0_47 != X1_47 | k1_relat_1(sK3) != X1_47 | k1_relat_1(sK3) = X0_47 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_876]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1722,plain,
% 2.06/0.99      ( X0_47 != k1_relat_1(sK3)
% 2.06/0.99      | k1_relat_1(sK3) = X0_47
% 2.06/0.99      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1509]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1724,plain,
% 2.06/0.99      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.06/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 2.06/0.99      | k1_xboole_0 != k1_relat_1(sK3) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1722]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2040,plain,
% 2.06/0.99      ( ~ r1_tarski(k1_relat_1(sK3),k1_enumset1(X0_50,X0_50,X0_50))
% 2.06/0.99      | k1_enumset1(X0_50,X0_50,X0_50) = k1_relat_1(sK3)
% 2.06/0.99      | k1_xboole_0 = k1_relat_1(sK3) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_867]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2048,plain,
% 2.06/0.99      ( ~ r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0))
% 2.06/0.99      | k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.06/0.99      | k1_xboole_0 = k1_relat_1(sK3) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_2040]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2275,plain,
% 2.06/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_2270,c_18,c_921,c_1303,c_1307,c_1305,c_1411,c_1477,c_1478,
% 2.06/0.99                 c_1685,c_1686,c_1724,c_2048]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_13,plain,
% 2.06/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_861,plain,
% 2.06/0.99      ( ~ v1_relat_1(X0_47)
% 2.06/0.99      | k1_relat_1(X0_47) != k1_xboole_0
% 2.06/0.99      | k1_xboole_0 = X0_47 ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1182,plain,
% 2.06/0.99      ( k1_relat_1(X0_47) != k1_xboole_0
% 2.06/0.99      | k1_xboole_0 = X0_47
% 2.06/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2287,plain,
% 2.06/0.99      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_2275,c_1182]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1993,plain,
% 2.06/0.99      ( ~ v1_relat_1(sK3)
% 2.06/0.99      | k1_relat_1(sK3) != k1_xboole_0
% 2.06/0.99      | k1_xboole_0 = sK3 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_861]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1687,plain,
% 2.06/0.99      ( X0_47 != X1_47 | sK3 != X1_47 | sK3 = X0_47 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_876]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2121,plain,
% 2.06/0.99      ( X0_47 != sK3 | sK3 = X0_47 | sK3 != sK3 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1687]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2122,plain,
% 2.06/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_2121]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2439,plain,
% 2.06/0.99      ( sK3 = k1_xboole_0 ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_2287,c_18,c_921,c_1303,c_1307,c_1305,c_1411,c_1477,c_1478,
% 2.06/0.99                 c_1685,c_1686,c_1724,c_1993,c_2048,c_2122]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1334,plain,
% 2.06/0.99      ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
% 2.06/0.99      inference(equality_resolution,[status(thm)],[c_855]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_860,negated_conjecture,
% 2.06/0.99      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1183,plain,
% 2.06/0.99      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1342,plain,
% 2.06/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.06/0.99      inference(demodulation,[status(thm)],[c_1334,c_1183]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2450,plain,
% 2.06/0.99      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.06/0.99      inference(demodulation,[status(thm)],[c_2439,c_1342]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4,plain,
% 2.06/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_409,plain,
% 2.06/0.99      ( v1_relat_1(X0)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 2.06/0.99      | k1_xboole_0 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_410,plain,
% 2.06/0.99      ( v1_relat_1(k1_xboole_0)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_856,plain,
% 2.06/0.99      ( v1_relat_1(k1_xboole_0)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_410]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1185,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
% 2.06/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1313,plain,
% 2.06/0.99      ( v1_relat_1(k1_xboole_0)
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_856]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1315,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 2.06/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1314,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) = k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_873]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1599,plain,
% 2.06/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_1185,c_1315,c_1314]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_8,plain,
% 2.06/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_865,plain,
% 2.06/0.99      ( ~ v1_relat_1(X0_47)
% 2.06/0.99      | k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1180,plain,
% 2.06/0.99      ( k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47)
% 2.06/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_865]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1800,plain,
% 2.06/0.99      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0_47)) = k9_relat_1(k1_xboole_0,X0_47) ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_1599,c_1180]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_10,plain,
% 2.06/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_864,plain,
% 2.06/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_9,plain,
% 2.06/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_321,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/0.99      | ~ v1_relat_1(X0)
% 2.06/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.06/0.99      inference(resolution,[status(thm)],[c_16,c_9]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_325,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.06/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_321,c_16,c_15,c_9]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_392,plain,
% 2.06/0.99      ( k7_relat_1(X0,X1) = X0
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 2.06/0.99      | k1_xboole_0 != X0 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_325]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_393,plain,
% 2.06/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 2.06/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_392]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_851,plain,
% 2.06/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
% 2.06/0.99      | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_393]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1408,plain,
% 2.06/0.99      ( k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 2.06/0.99      inference(equality_resolution,[status(thm)],[c_851]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1805,plain,
% 2.06/0.99      ( k9_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 2.06/0.99      inference(light_normalisation,[status(thm)],[c_1800,c_864,c_1408]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2463,plain,
% 2.06/0.99      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.06/0.99      inference(demodulation,[status(thm)],[c_2450,c_1805]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_0,plain,
% 2.06/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_870,plain,
% 2.06/0.99      ( r1_tarski(k1_xboole_0,X0_47) ),
% 2.06/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1175,plain,
% 2.06/0.99      ( r1_tarski(k1_xboole_0,X0_47) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_870]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2475,plain,
% 2.06/0.99      ( $false ),
% 2.06/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2463,c_1175]) ).
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  ------                               Statistics
% 2.06/0.99  
% 2.06/0.99  ------ General
% 2.06/0.99  
% 2.06/0.99  abstr_ref_over_cycles:                  0
% 2.06/0.99  abstr_ref_under_cycles:                 0
% 2.06/0.99  gc_basic_clause_elim:                   0
% 2.06/0.99  forced_gc_time:                         0
% 2.06/0.99  parsing_time:                           0.008
% 2.06/0.99  unif_index_cands_time:                  0.
% 2.06/0.99  unif_index_add_time:                    0.
% 2.06/0.99  orderings_time:                         0.
% 2.06/0.99  out_proof_time:                         0.013
% 2.06/0.99  total_time:                             0.107
% 2.06/0.99  num_of_symbols:                         54
% 2.06/0.99  num_of_terms:                           2340
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing
% 2.06/0.99  
% 2.06/0.99  num_of_splits:                          0
% 2.06/0.99  num_of_split_atoms:                     0
% 2.06/0.99  num_of_reused_defs:                     0
% 2.06/0.99  num_eq_ax_congr_red:                    9
% 2.06/0.99  num_of_sem_filtered_clauses:            1
% 2.06/0.99  num_of_subtypes:                        4
% 2.06/0.99  monotx_restored_types:                  0
% 2.06/0.99  sat_num_of_epr_types:                   0
% 2.06/0.99  sat_num_of_non_cyclic_types:            0
% 2.06/0.99  sat_guarded_non_collapsed_types:        1
% 2.06/0.99  num_pure_diseq_elim:                    0
% 2.06/0.99  simp_replaced_by:                       0
% 2.06/0.99  res_preprocessed:                       101
% 2.06/0.99  prep_upred:                             0
% 2.06/0.99  prep_unflattend:                        43
% 2.06/0.99  smt_new_axioms:                         0
% 2.06/0.99  pred_elim_cands:                        5
% 2.06/0.99  pred_elim:                              3
% 2.06/0.99  pred_elim_cl:                           0
% 2.06/0.99  pred_elim_cycles:                       6
% 2.06/0.99  merged_defs:                            0
% 2.06/0.99  merged_defs_ncl:                        0
% 2.06/0.99  bin_hyper_res:                          0
% 2.06/0.99  prep_cycles:                            3
% 2.06/0.99  pred_elim_time:                         0.011
% 2.06/0.99  splitting_time:                         0.
% 2.06/0.99  sem_filter_time:                        0.
% 2.06/0.99  monotx_time:                            0.
% 2.06/0.99  subtype_inf_time:                       0.
% 2.06/0.99  
% 2.06/0.99  ------ Problem properties
% 2.06/0.99  
% 2.06/0.99  clauses:                                22
% 2.06/0.99  conjectures:                            2
% 2.06/0.99  epr:                                    2
% 2.06/0.99  horn:                                   21
% 2.06/0.99  ground:                                 4
% 2.06/0.99  unary:                                  7
% 2.06/0.99  binary:                                 10
% 2.06/0.99  lits:                                   42
% 2.06/0.99  lits_eq:                                25
% 2.06/0.99  fd_pure:                                0
% 2.06/0.99  fd_pseudo:                              0
% 2.06/0.99  fd_cond:                                2
% 2.06/0.99  fd_pseudo_cond:                         1
% 2.06/0.99  ac_symbols:                             0
% 2.06/0.99  
% 2.06/0.99  ------ Propositional Solver
% 2.06/0.99  
% 2.06/0.99  prop_solver_calls:                      23
% 2.06/0.99  prop_fast_solver_calls:                 607
% 2.06/0.99  smt_solver_calls:                       0
% 2.06/0.99  smt_fast_solver_calls:                  0
% 2.06/0.99  prop_num_of_clauses:                    798
% 2.06/0.99  prop_preprocess_simplified:             3254
% 2.06/0.99  prop_fo_subsumed:                       11
% 2.06/0.99  prop_solver_time:                       0.
% 2.06/0.99  smt_solver_time:                        0.
% 2.06/0.99  smt_fast_solver_time:                   0.
% 2.06/0.99  prop_fast_solver_time:                  0.
% 2.06/0.99  prop_unsat_core_time:                   0.
% 2.06/0.99  
% 2.06/0.99  ------ QBF
% 2.06/0.99  
% 2.06/0.99  qbf_q_res:                              0
% 2.06/0.99  qbf_num_tautologies:                    0
% 2.06/0.99  qbf_prep_cycles:                        0
% 2.06/0.99  
% 2.06/0.99  ------ BMC1
% 2.06/0.99  
% 2.06/0.99  bmc1_current_bound:                     -1
% 2.06/0.99  bmc1_last_solved_bound:                 -1
% 2.06/0.99  bmc1_unsat_core_size:                   -1
% 2.06/0.99  bmc1_unsat_core_parents_size:           -1
% 2.06/0.99  bmc1_merge_next_fun:                    0
% 2.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation
% 2.06/0.99  
% 2.06/0.99  inst_num_of_clauses:                    257
% 2.06/0.99  inst_num_in_passive:                    51
% 2.06/0.99  inst_num_in_active:                     171
% 2.06/0.99  inst_num_in_unprocessed:                35
% 2.06/0.99  inst_num_of_loops:                      180
% 2.06/0.99  inst_num_of_learning_restarts:          0
% 2.06/0.99  inst_num_moves_active_passive:          6
% 2.06/0.99  inst_lit_activity:                      0
% 2.06/0.99  inst_lit_activity_moves:                0
% 2.06/0.99  inst_num_tautologies:                   0
% 2.06/0.99  inst_num_prop_implied:                  0
% 2.06/0.99  inst_num_existing_simplified:           0
% 2.06/0.99  inst_num_eq_res_simplified:             0
% 2.06/0.99  inst_num_child_elim:                    0
% 2.06/0.99  inst_num_of_dismatching_blockings:      42
% 2.06/0.99  inst_num_of_non_proper_insts:           200
% 2.06/0.99  inst_num_of_duplicates:                 0
% 2.06/0.99  inst_inst_num_from_inst_to_res:         0
% 2.06/0.99  inst_dismatching_checking_time:         0.
% 2.06/0.99  
% 2.06/0.99  ------ Resolution
% 2.06/0.99  
% 2.06/0.99  res_num_of_clauses:                     0
% 2.06/0.99  res_num_in_passive:                     0
% 2.06/0.99  res_num_in_active:                      0
% 2.06/0.99  res_num_of_loops:                       104
% 2.06/0.99  res_forward_subset_subsumed:            50
% 2.06/0.99  res_backward_subset_subsumed:           2
% 2.06/0.99  res_forward_subsumed:                   1
% 2.06/0.99  res_backward_subsumed:                  0
% 2.06/0.99  res_forward_subsumption_resolution:     0
% 2.06/0.99  res_backward_subsumption_resolution:    0
% 2.06/0.99  res_clause_to_clause_subsumption:       56
% 2.06/0.99  res_orphan_elimination:                 0
% 2.06/0.99  res_tautology_del:                      44
% 2.06/0.99  res_num_eq_res_simplified:              0
% 2.06/0.99  res_num_sel_changes:                    0
% 2.06/0.99  res_moves_from_active_to_pass:          0
% 2.06/0.99  
% 2.06/0.99  ------ Superposition
% 2.06/0.99  
% 2.06/0.99  sup_time_total:                         0.
% 2.06/0.99  sup_time_generating:                    0.
% 2.06/0.99  sup_time_sim_full:                      0.
% 2.06/0.99  sup_time_sim_immed:                     0.
% 2.06/0.99  
% 2.06/0.99  sup_num_of_clauses:                     20
% 2.06/0.99  sup_num_in_active:                      15
% 2.06/0.99  sup_num_in_passive:                     5
% 2.06/0.99  sup_num_of_loops:                       35
% 2.06/0.99  sup_fw_superposition:                   12
% 2.06/0.99  sup_bw_superposition:                   5
% 2.06/0.99  sup_immediate_simplified:               17
% 2.06/0.99  sup_given_eliminated:                   0
% 2.06/0.99  comparisons_done:                       0
% 2.06/0.99  comparisons_avoided:                    0
% 2.06/0.99  
% 2.06/0.99  ------ Simplifications
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  sim_fw_subset_subsumed:                 3
% 2.06/0.99  sim_bw_subset_subsumed:                 0
% 2.06/0.99  sim_fw_subsumed:                        10
% 2.06/0.99  sim_bw_subsumed:                        0
% 2.06/0.99  sim_fw_subsumption_res:                 1
% 2.06/0.99  sim_bw_subsumption_res:                 0
% 2.06/0.99  sim_tautology_del:                      0
% 2.06/0.99  sim_eq_tautology_del:                   6
% 2.06/0.99  sim_eq_res_simp:                        0
% 2.06/0.99  sim_fw_demodulated:                     3
% 2.06/0.99  sim_bw_demodulated:                     20
% 2.06/0.99  sim_light_normalised:                   11
% 2.06/0.99  sim_joinable_taut:                      0
% 2.06/0.99  sim_joinable_simp:                      0
% 2.06/0.99  sim_ac_normalised:                      0
% 2.06/0.99  sim_smt_subsumption:                    0
% 2.06/0.99  
%------------------------------------------------------------------------------
