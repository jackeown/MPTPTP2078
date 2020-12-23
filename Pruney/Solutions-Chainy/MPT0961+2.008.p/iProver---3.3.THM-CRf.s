%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:56 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 579 expanded)
%              Number of clauses        :   60 ( 193 expanded)
%              Number of leaves         :    9 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  314 (2374 expanded)
%              Number of equality atoms :  167 ( 679 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f30])).

fof(f55,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f60])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_124,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_22])).

cnf(c_125,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_relat_1(sK0) != X2
    | k1_relat_1(sK0) != X1
    | sK0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_125])).

cnf(c_599,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_607,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_599,c_14])).

cnf(c_1138,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_323,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_324,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1250,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1259,plain,
    ( k1_xboole_0 = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1138,c_324,c_607,c_1250])).

cnf(c_1145,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1803,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_1145])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1807,plain,
    ( r1_tarski(sK0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1803,c_4])).

cnf(c_24,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1912,plain,
    ( r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1807,c_24])).

cnf(c_1147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1143,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2003,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1143])).

cnf(c_2124,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_2003])).

cnf(c_2317,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK0) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_1912,c_2124])).

cnf(c_17,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_relat_1(sK0) != X1
    | k1_relat_1(sK0) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_125])).

cnf(c_583,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_1139,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1201,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1139,c_5])).

cnf(c_325,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_1251,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) = iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_1280,plain,
    ( k1_relat_1(sK0) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1201,c_325,c_1251])).

cnf(c_1281,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1280])).

cnf(c_1284,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1281,c_1259])).

cnf(c_2368,plain,
    ( k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2317,c_1284])).

cnf(c_1392,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1393,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1381,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1384,plain,
    ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1296,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1297,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_15,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_555,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k2_relat_1(sK0) != k1_xboole_0
    | k1_relat_1(sK0) != X0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_125])).

cnf(c_556,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_1140,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_1210,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1140,c_4])).

cnf(c_67,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_72,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1226,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k2_relat_1(sK0) != k1_xboole_0
    | k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1210])).

cnf(c_1290,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_67,c_72,c_324,c_1226,c_1250])).

cnf(c_1292,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1290,c_1259])).

cnf(c_1293,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1292])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2368,c_1807,c_1393,c_1384,c_1297,c_1293,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.72/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.01  
% 1.72/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.72/1.01  
% 1.72/1.01  ------  iProver source info
% 1.72/1.01  
% 1.72/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.72/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.72/1.01  git: non_committed_changes: false
% 1.72/1.01  git: last_make_outside_of_git: false
% 1.72/1.01  
% 1.72/1.01  ------ 
% 1.72/1.01  
% 1.72/1.01  ------ Input Options
% 1.72/1.01  
% 1.72/1.01  --out_options                           all
% 1.72/1.01  --tptp_safe_out                         true
% 1.72/1.01  --problem_path                          ""
% 1.72/1.01  --include_path                          ""
% 1.72/1.01  --clausifier                            res/vclausify_rel
% 1.72/1.01  --clausifier_options                    --mode clausify
% 1.72/1.01  --stdin                                 false
% 1.72/1.01  --stats_out                             all
% 1.72/1.01  
% 1.72/1.01  ------ General Options
% 1.72/1.01  
% 1.72/1.01  --fof                                   false
% 1.72/1.01  --time_out_real                         305.
% 1.72/1.01  --time_out_virtual                      -1.
% 1.72/1.01  --symbol_type_check                     false
% 1.72/1.01  --clausify_out                          false
% 1.72/1.01  --sig_cnt_out                           false
% 1.72/1.01  --trig_cnt_out                          false
% 1.72/1.01  --trig_cnt_out_tolerance                1.
% 1.72/1.01  --trig_cnt_out_sk_spl                   false
% 1.72/1.01  --abstr_cl_out                          false
% 1.72/1.01  
% 1.72/1.01  ------ Global Options
% 1.72/1.01  
% 1.72/1.01  --schedule                              default
% 1.72/1.01  --add_important_lit                     false
% 1.72/1.01  --prop_solver_per_cl                    1000
% 1.72/1.01  --min_unsat_core                        false
% 1.72/1.01  --soft_assumptions                      false
% 1.72/1.01  --soft_lemma_size                       3
% 1.72/1.01  --prop_impl_unit_size                   0
% 1.72/1.01  --prop_impl_unit                        []
% 1.72/1.01  --share_sel_clauses                     true
% 1.72/1.01  --reset_solvers                         false
% 1.72/1.01  --bc_imp_inh                            [conj_cone]
% 1.72/1.01  --conj_cone_tolerance                   3.
% 1.72/1.01  --extra_neg_conj                        none
% 1.72/1.01  --large_theory_mode                     true
% 1.72/1.01  --prolific_symb_bound                   200
% 1.72/1.01  --lt_threshold                          2000
% 1.72/1.01  --clause_weak_htbl                      true
% 1.72/1.01  --gc_record_bc_elim                     false
% 1.72/1.01  
% 1.72/1.01  ------ Preprocessing Options
% 1.72/1.01  
% 1.72/1.01  --preprocessing_flag                    true
% 1.72/1.01  --time_out_prep_mult                    0.1
% 1.72/1.01  --splitting_mode                        input
% 1.72/1.01  --splitting_grd                         true
% 1.72/1.01  --splitting_cvd                         false
% 1.72/1.01  --splitting_cvd_svl                     false
% 1.72/1.01  --splitting_nvd                         32
% 1.72/1.01  --sub_typing                            true
% 1.72/1.01  --prep_gs_sim                           true
% 1.72/1.01  --prep_unflatten                        true
% 1.72/1.01  --prep_res_sim                          true
% 1.72/1.01  --prep_upred                            true
% 1.72/1.01  --prep_sem_filter                       exhaustive
% 1.72/1.01  --prep_sem_filter_out                   false
% 1.72/1.01  --pred_elim                             true
% 1.72/1.01  --res_sim_input                         true
% 1.72/1.01  --eq_ax_congr_red                       true
% 1.72/1.01  --pure_diseq_elim                       true
% 1.72/1.01  --brand_transform                       false
% 1.72/1.01  --non_eq_to_eq                          false
% 1.72/1.01  --prep_def_merge                        true
% 1.72/1.01  --prep_def_merge_prop_impl              false
% 1.72/1.01  --prep_def_merge_mbd                    true
% 1.72/1.01  --prep_def_merge_tr_red                 false
% 1.72/1.01  --prep_def_merge_tr_cl                  false
% 1.72/1.01  --smt_preprocessing                     true
% 1.72/1.01  --smt_ac_axioms                         fast
% 1.72/1.01  --preprocessed_out                      false
% 1.72/1.01  --preprocessed_stats                    false
% 1.72/1.01  
% 1.72/1.01  ------ Abstraction refinement Options
% 1.72/1.01  
% 1.72/1.01  --abstr_ref                             []
% 1.72/1.01  --abstr_ref_prep                        false
% 1.72/1.01  --abstr_ref_until_sat                   false
% 1.72/1.01  --abstr_ref_sig_restrict                funpre
% 1.72/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/1.01  --abstr_ref_under                       []
% 1.72/1.01  
% 1.72/1.01  ------ SAT Options
% 1.72/1.01  
% 1.72/1.01  --sat_mode                              false
% 1.72/1.01  --sat_fm_restart_options                ""
% 1.72/1.01  --sat_gr_def                            false
% 1.72/1.01  --sat_epr_types                         true
% 1.72/1.01  --sat_non_cyclic_types                  false
% 1.72/1.01  --sat_finite_models                     false
% 1.72/1.01  --sat_fm_lemmas                         false
% 1.72/1.01  --sat_fm_prep                           false
% 1.72/1.01  --sat_fm_uc_incr                        true
% 1.72/1.01  --sat_out_model                         small
% 1.72/1.01  --sat_out_clauses                       false
% 1.72/1.01  
% 1.72/1.01  ------ QBF Options
% 1.72/1.01  
% 1.72/1.01  --qbf_mode                              false
% 1.72/1.01  --qbf_elim_univ                         false
% 1.72/1.01  --qbf_dom_inst                          none
% 1.72/1.01  --qbf_dom_pre_inst                      false
% 1.72/1.01  --qbf_sk_in                             false
% 1.72/1.01  --qbf_pred_elim                         true
% 1.72/1.01  --qbf_split                             512
% 1.72/1.01  
% 1.72/1.01  ------ BMC1 Options
% 1.72/1.01  
% 1.72/1.01  --bmc1_incremental                      false
% 1.72/1.01  --bmc1_axioms                           reachable_all
% 1.72/1.01  --bmc1_min_bound                        0
% 1.72/1.01  --bmc1_max_bound                        -1
% 1.72/1.01  --bmc1_max_bound_default                -1
% 1.72/1.01  --bmc1_symbol_reachability              true
% 1.72/1.01  --bmc1_property_lemmas                  false
% 1.72/1.01  --bmc1_k_induction                      false
% 1.72/1.01  --bmc1_non_equiv_states                 false
% 1.72/1.01  --bmc1_deadlock                         false
% 1.72/1.01  --bmc1_ucm                              false
% 1.72/1.01  --bmc1_add_unsat_core                   none
% 1.72/1.01  --bmc1_unsat_core_children              false
% 1.72/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/1.01  --bmc1_out_stat                         full
% 1.72/1.01  --bmc1_ground_init                      false
% 1.72/1.01  --bmc1_pre_inst_next_state              false
% 1.72/1.01  --bmc1_pre_inst_state                   false
% 1.72/1.01  --bmc1_pre_inst_reach_state             false
% 1.72/1.01  --bmc1_out_unsat_core                   false
% 1.72/1.01  --bmc1_aig_witness_out                  false
% 1.72/1.01  --bmc1_verbose                          false
% 1.72/1.01  --bmc1_dump_clauses_tptp                false
% 1.72/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.72/1.01  --bmc1_dump_file                        -
% 1.72/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.72/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.72/1.01  --bmc1_ucm_extend_mode                  1
% 1.72/1.01  --bmc1_ucm_init_mode                    2
% 1.72/1.01  --bmc1_ucm_cone_mode                    none
% 1.72/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.72/1.01  --bmc1_ucm_relax_model                  4
% 1.72/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.72/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/1.01  --bmc1_ucm_layered_model                none
% 1.72/1.01  --bmc1_ucm_max_lemma_size               10
% 1.72/1.01  
% 1.72/1.01  ------ AIG Options
% 1.72/1.01  
% 1.72/1.01  --aig_mode                              false
% 1.72/1.01  
% 1.72/1.01  ------ Instantiation Options
% 1.72/1.01  
% 1.72/1.01  --instantiation_flag                    true
% 1.72/1.01  --inst_sos_flag                         false
% 1.72/1.01  --inst_sos_phase                        true
% 1.72/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/1.01  --inst_lit_sel_side                     num_symb
% 1.72/1.01  --inst_solver_per_active                1400
% 1.72/1.01  --inst_solver_calls_frac                1.
% 1.72/1.01  --inst_passive_queue_type               priority_queues
% 1.72/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/1.01  --inst_passive_queues_freq              [25;2]
% 1.72/1.01  --inst_dismatching                      true
% 1.72/1.01  --inst_eager_unprocessed_to_passive     true
% 1.72/1.01  --inst_prop_sim_given                   true
% 1.72/1.01  --inst_prop_sim_new                     false
% 1.72/1.01  --inst_subs_new                         false
% 1.72/1.01  --inst_eq_res_simp                      false
% 1.72/1.01  --inst_subs_given                       false
% 1.72/1.01  --inst_orphan_elimination               true
% 1.72/1.01  --inst_learning_loop_flag               true
% 1.72/1.01  --inst_learning_start                   3000
% 1.72/1.01  --inst_learning_factor                  2
% 1.72/1.01  --inst_start_prop_sim_after_learn       3
% 1.72/1.01  --inst_sel_renew                        solver
% 1.72/1.01  --inst_lit_activity_flag                true
% 1.72/1.01  --inst_restr_to_given                   false
% 1.72/1.01  --inst_activity_threshold               500
% 1.72/1.01  --inst_out_proof                        true
% 1.72/1.01  
% 1.72/1.01  ------ Resolution Options
% 1.72/1.01  
% 1.72/1.01  --resolution_flag                       true
% 1.72/1.01  --res_lit_sel                           adaptive
% 1.72/1.01  --res_lit_sel_side                      none
% 1.72/1.01  --res_ordering                          kbo
% 1.72/1.01  --res_to_prop_solver                    active
% 1.72/1.01  --res_prop_simpl_new                    false
% 1.72/1.01  --res_prop_simpl_given                  true
% 1.72/1.01  --res_passive_queue_type                priority_queues
% 1.72/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/1.01  --res_passive_queues_freq               [15;5]
% 1.72/1.01  --res_forward_subs                      full
% 1.72/1.01  --res_backward_subs                     full
% 1.72/1.01  --res_forward_subs_resolution           true
% 1.72/1.01  --res_backward_subs_resolution          true
% 1.72/1.01  --res_orphan_elimination                true
% 1.72/1.01  --res_time_limit                        2.
% 1.72/1.01  --res_out_proof                         true
% 1.72/1.01  
% 1.72/1.01  ------ Superposition Options
% 1.72/1.01  
% 1.72/1.01  --superposition_flag                    true
% 1.72/1.01  --sup_passive_queue_type                priority_queues
% 1.72/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.72/1.01  --demod_completeness_check              fast
% 1.72/1.01  --demod_use_ground                      true
% 1.72/1.01  --sup_to_prop_solver                    passive
% 1.72/1.01  --sup_prop_simpl_new                    true
% 1.72/1.01  --sup_prop_simpl_given                  true
% 1.72/1.01  --sup_fun_splitting                     false
% 1.72/1.01  --sup_smt_interval                      50000
% 1.72/1.01  
% 1.72/1.01  ------ Superposition Simplification Setup
% 1.72/1.01  
% 1.72/1.01  --sup_indices_passive                   []
% 1.72/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.01  --sup_full_bw                           [BwDemod]
% 1.72/1.01  --sup_immed_triv                        [TrivRules]
% 1.72/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.01  --sup_immed_bw_main                     []
% 1.72/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.01  
% 1.72/1.01  ------ Combination Options
% 1.72/1.01  
% 1.72/1.01  --comb_res_mult                         3
% 1.72/1.01  --comb_sup_mult                         2
% 1.72/1.01  --comb_inst_mult                        10
% 1.72/1.01  
% 1.72/1.01  ------ Debug Options
% 1.72/1.01  
% 1.72/1.01  --dbg_backtrace                         false
% 1.72/1.01  --dbg_dump_prop_clauses                 false
% 1.72/1.01  --dbg_dump_prop_clauses_file            -
% 1.72/1.01  --dbg_out_stat                          false
% 1.72/1.01  ------ Parsing...
% 1.72/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.72/1.01  
% 1.72/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.72/1.01  
% 1.72/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.72/1.01  
% 1.72/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.72/1.01  ------ Proving...
% 1.72/1.01  ------ Problem Properties 
% 1.72/1.01  
% 1.72/1.01  
% 1.72/1.01  clauses                                 16
% 1.72/1.01  conjectures                             1
% 1.72/1.01  EPR                                     4
% 1.72/1.01  Horn                                    15
% 1.72/1.01  unary                                   5
% 1.72/1.01  binary                                  7
% 1.72/1.01  lits                                    34
% 1.72/1.01  lits eq                                 13
% 1.72/1.01  fd_pure                                 0
% 1.72/1.01  fd_pseudo                               0
% 1.72/1.01  fd_cond                                 1
% 1.72/1.01  fd_pseudo_cond                          1
% 1.72/1.01  AC symbols                              0
% 1.72/1.01  
% 1.72/1.01  ------ Schedule dynamic 5 is on 
% 1.72/1.01  
% 1.72/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.72/1.01  
% 1.72/1.01  
% 1.72/1.01  ------ 
% 1.72/1.01  Current options:
% 1.72/1.01  ------ 
% 1.72/1.01  
% 1.72/1.01  ------ Input Options
% 1.72/1.01  
% 1.72/1.01  --out_options                           all
% 1.72/1.01  --tptp_safe_out                         true
% 1.72/1.01  --problem_path                          ""
% 1.72/1.01  --include_path                          ""
% 1.72/1.01  --clausifier                            res/vclausify_rel
% 1.72/1.01  --clausifier_options                    --mode clausify
% 1.72/1.01  --stdin                                 false
% 1.72/1.01  --stats_out                             all
% 1.72/1.01  
% 1.72/1.01  ------ General Options
% 1.72/1.01  
% 1.72/1.01  --fof                                   false
% 1.72/1.01  --time_out_real                         305.
% 1.72/1.01  --time_out_virtual                      -1.
% 1.72/1.01  --symbol_type_check                     false
% 1.72/1.01  --clausify_out                          false
% 1.72/1.01  --sig_cnt_out                           false
% 1.72/1.01  --trig_cnt_out                          false
% 1.72/1.01  --trig_cnt_out_tolerance                1.
% 1.72/1.01  --trig_cnt_out_sk_spl                   false
% 1.72/1.01  --abstr_cl_out                          false
% 1.72/1.01  
% 1.72/1.01  ------ Global Options
% 1.72/1.01  
% 1.72/1.01  --schedule                              default
% 1.72/1.01  --add_important_lit                     false
% 1.72/1.01  --prop_solver_per_cl                    1000
% 1.72/1.01  --min_unsat_core                        false
% 1.72/1.01  --soft_assumptions                      false
% 1.72/1.01  --soft_lemma_size                       3
% 1.72/1.01  --prop_impl_unit_size                   0
% 1.72/1.01  --prop_impl_unit                        []
% 1.72/1.01  --share_sel_clauses                     true
% 1.72/1.01  --reset_solvers                         false
% 1.72/1.01  --bc_imp_inh                            [conj_cone]
% 1.72/1.01  --conj_cone_tolerance                   3.
% 1.72/1.01  --extra_neg_conj                        none
% 1.72/1.01  --large_theory_mode                     true
% 1.72/1.01  --prolific_symb_bound                   200
% 1.72/1.01  --lt_threshold                          2000
% 1.72/1.01  --clause_weak_htbl                      true
% 1.72/1.01  --gc_record_bc_elim                     false
% 1.72/1.01  
% 1.72/1.01  ------ Preprocessing Options
% 1.72/1.01  
% 1.72/1.01  --preprocessing_flag                    true
% 1.72/1.01  --time_out_prep_mult                    0.1
% 1.72/1.01  --splitting_mode                        input
% 1.72/1.01  --splitting_grd                         true
% 1.72/1.01  --splitting_cvd                         false
% 1.72/1.01  --splitting_cvd_svl                     false
% 1.72/1.01  --splitting_nvd                         32
% 1.72/1.01  --sub_typing                            true
% 1.72/1.01  --prep_gs_sim                           true
% 1.72/1.01  --prep_unflatten                        true
% 1.72/1.01  --prep_res_sim                          true
% 1.72/1.01  --prep_upred                            true
% 1.72/1.01  --prep_sem_filter                       exhaustive
% 1.72/1.01  --prep_sem_filter_out                   false
% 1.72/1.01  --pred_elim                             true
% 1.72/1.01  --res_sim_input                         true
% 1.72/1.01  --eq_ax_congr_red                       true
% 1.72/1.01  --pure_diseq_elim                       true
% 1.72/1.01  --brand_transform                       false
% 1.72/1.01  --non_eq_to_eq                          false
% 1.72/1.01  --prep_def_merge                        true
% 1.72/1.01  --prep_def_merge_prop_impl              false
% 1.72/1.01  --prep_def_merge_mbd                    true
% 1.72/1.01  --prep_def_merge_tr_red                 false
% 1.72/1.01  --prep_def_merge_tr_cl                  false
% 1.72/1.01  --smt_preprocessing                     true
% 1.72/1.01  --smt_ac_axioms                         fast
% 1.72/1.01  --preprocessed_out                      false
% 1.72/1.01  --preprocessed_stats                    false
% 1.72/1.01  
% 1.72/1.01  ------ Abstraction refinement Options
% 1.72/1.01  
% 1.72/1.01  --abstr_ref                             []
% 1.72/1.01  --abstr_ref_prep                        false
% 1.72/1.01  --abstr_ref_until_sat                   false
% 1.72/1.01  --abstr_ref_sig_restrict                funpre
% 1.72/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/1.01  --abstr_ref_under                       []
% 1.72/1.01  
% 1.72/1.01  ------ SAT Options
% 1.72/1.01  
% 1.72/1.01  --sat_mode                              false
% 1.72/1.01  --sat_fm_restart_options                ""
% 1.72/1.01  --sat_gr_def                            false
% 1.72/1.01  --sat_epr_types                         true
% 1.72/1.01  --sat_non_cyclic_types                  false
% 1.72/1.01  --sat_finite_models                     false
% 1.72/1.01  --sat_fm_lemmas                         false
% 1.72/1.01  --sat_fm_prep                           false
% 1.72/1.01  --sat_fm_uc_incr                        true
% 1.72/1.01  --sat_out_model                         small
% 1.72/1.01  --sat_out_clauses                       false
% 1.72/1.01  
% 1.72/1.01  ------ QBF Options
% 1.72/1.01  
% 1.72/1.01  --qbf_mode                              false
% 1.72/1.01  --qbf_elim_univ                         false
% 1.72/1.01  --qbf_dom_inst                          none
% 1.72/1.01  --qbf_dom_pre_inst                      false
% 1.72/1.01  --qbf_sk_in                             false
% 1.72/1.01  --qbf_pred_elim                         true
% 1.72/1.01  --qbf_split                             512
% 1.72/1.01  
% 1.72/1.01  ------ BMC1 Options
% 1.72/1.01  
% 1.72/1.01  --bmc1_incremental                      false
% 1.72/1.01  --bmc1_axioms                           reachable_all
% 1.72/1.01  --bmc1_min_bound                        0
% 1.72/1.01  --bmc1_max_bound                        -1
% 1.72/1.01  --bmc1_max_bound_default                -1
% 1.72/1.01  --bmc1_symbol_reachability              true
% 1.72/1.01  --bmc1_property_lemmas                  false
% 1.72/1.01  --bmc1_k_induction                      false
% 1.72/1.01  --bmc1_non_equiv_states                 false
% 1.72/1.01  --bmc1_deadlock                         false
% 1.72/1.01  --bmc1_ucm                              false
% 1.72/1.01  --bmc1_add_unsat_core                   none
% 1.72/1.01  --bmc1_unsat_core_children              false
% 1.72/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/1.01  --bmc1_out_stat                         full
% 1.72/1.01  --bmc1_ground_init                      false
% 1.72/1.01  --bmc1_pre_inst_next_state              false
% 1.72/1.01  --bmc1_pre_inst_state                   false
% 1.72/1.01  --bmc1_pre_inst_reach_state             false
% 1.72/1.01  --bmc1_out_unsat_core                   false
% 1.72/1.01  --bmc1_aig_witness_out                  false
% 1.72/1.01  --bmc1_verbose                          false
% 1.72/1.01  --bmc1_dump_clauses_tptp                false
% 1.72/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.72/1.01  --bmc1_dump_file                        -
% 1.72/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.72/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.72/1.01  --bmc1_ucm_extend_mode                  1
% 1.72/1.01  --bmc1_ucm_init_mode                    2
% 1.72/1.01  --bmc1_ucm_cone_mode                    none
% 1.72/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.72/1.01  --bmc1_ucm_relax_model                  4
% 1.72/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.72/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/1.01  --bmc1_ucm_layered_model                none
% 1.72/1.01  --bmc1_ucm_max_lemma_size               10
% 1.72/1.01  
% 1.72/1.01  ------ AIG Options
% 1.72/1.01  
% 1.72/1.01  --aig_mode                              false
% 1.72/1.01  
% 1.72/1.01  ------ Instantiation Options
% 1.72/1.01  
% 1.72/1.01  --instantiation_flag                    true
% 1.72/1.01  --inst_sos_flag                         false
% 1.72/1.01  --inst_sos_phase                        true
% 1.72/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/1.01  --inst_lit_sel_side                     none
% 1.72/1.01  --inst_solver_per_active                1400
% 1.72/1.01  --inst_solver_calls_frac                1.
% 1.72/1.01  --inst_passive_queue_type               priority_queues
% 1.72/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/1.01  --inst_passive_queues_freq              [25;2]
% 1.72/1.01  --inst_dismatching                      true
% 1.72/1.01  --inst_eager_unprocessed_to_passive     true
% 1.72/1.01  --inst_prop_sim_given                   true
% 1.72/1.01  --inst_prop_sim_new                     false
% 1.72/1.01  --inst_subs_new                         false
% 1.72/1.01  --inst_eq_res_simp                      false
% 1.72/1.01  --inst_subs_given                       false
% 1.72/1.01  --inst_orphan_elimination               true
% 1.72/1.01  --inst_learning_loop_flag               true
% 1.72/1.01  --inst_learning_start                   3000
% 1.72/1.01  --inst_learning_factor                  2
% 1.72/1.01  --inst_start_prop_sim_after_learn       3
% 1.72/1.01  --inst_sel_renew                        solver
% 1.72/1.01  --inst_lit_activity_flag                true
% 1.72/1.01  --inst_restr_to_given                   false
% 1.72/1.01  --inst_activity_threshold               500
% 1.72/1.01  --inst_out_proof                        true
% 1.72/1.01  
% 1.72/1.01  ------ Resolution Options
% 1.72/1.01  
% 1.72/1.01  --resolution_flag                       false
% 1.72/1.01  --res_lit_sel                           adaptive
% 1.72/1.01  --res_lit_sel_side                      none
% 1.72/1.01  --res_ordering                          kbo
% 1.72/1.01  --res_to_prop_solver                    active
% 1.72/1.01  --res_prop_simpl_new                    false
% 1.72/1.01  --res_prop_simpl_given                  true
% 1.72/1.01  --res_passive_queue_type                priority_queues
% 1.72/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/1.01  --res_passive_queues_freq               [15;5]
% 1.72/1.01  --res_forward_subs                      full
% 1.72/1.01  --res_backward_subs                     full
% 1.72/1.01  --res_forward_subs_resolution           true
% 1.72/1.01  --res_backward_subs_resolution          true
% 1.72/1.01  --res_orphan_elimination                true
% 1.72/1.01  --res_time_limit                        2.
% 1.72/1.01  --res_out_proof                         true
% 1.72/1.01  
% 1.72/1.01  ------ Superposition Options
% 1.72/1.01  
% 1.72/1.01  --superposition_flag                    true
% 1.72/1.01  --sup_passive_queue_type                priority_queues
% 1.72/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.72/1.01  --demod_completeness_check              fast
% 1.72/1.01  --demod_use_ground                      true
% 1.72/1.01  --sup_to_prop_solver                    passive
% 1.72/1.01  --sup_prop_simpl_new                    true
% 1.72/1.01  --sup_prop_simpl_given                  true
% 1.72/1.01  --sup_fun_splitting                     false
% 1.72/1.01  --sup_smt_interval                      50000
% 1.72/1.01  
% 1.72/1.01  ------ Superposition Simplification Setup
% 1.72/1.01  
% 1.72/1.01  --sup_indices_passive                   []
% 1.72/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.01  --sup_full_bw                           [BwDemod]
% 1.72/1.01  --sup_immed_triv                        [TrivRules]
% 1.72/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.01  --sup_immed_bw_main                     []
% 1.72/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/1.01  
% 1.72/1.01  ------ Combination Options
% 1.72/1.01  
% 1.72/1.01  --comb_res_mult                         3
% 1.72/1.01  --comb_sup_mult                         2
% 1.72/1.01  --comb_inst_mult                        10
% 1.72/1.01  
% 1.72/1.01  ------ Debug Options
% 1.72/1.01  
% 1.72/1.01  --dbg_backtrace                         false
% 1.72/1.01  --dbg_dump_prop_clauses                 false
% 1.72/1.01  --dbg_dump_prop_clauses_file            -
% 1.72/1.01  --dbg_out_stat                          false
% 1.72/1.01  
% 1.72/1.01  
% 1.72/1.01  
% 1.72/1.01  
% 1.72/1.01  ------ Proving...
% 1.72/1.01  
% 1.72/1.01  
% 1.72/1.01  % SZS status Theorem for theBenchmark.p
% 1.72/1.01  
% 1.72/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.72/1.01  
% 1.72/1.01  fof(f10,axiom,(
% 1.72/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.72/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.01  
% 1.72/1.01  fof(f19,plain,(
% 1.72/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.01    inference(ennf_transformation,[],[f10])).
% 1.72/1.01  
% 1.72/1.01  fof(f20,plain,(
% 1.72/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.01    inference(flattening,[],[f19])).
% 1.72/1.01  
% 1.72/1.01  fof(f29,plain,(
% 1.72/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.01    inference(nnf_transformation,[],[f20])).
% 1.72/1.01  
% 1.72/1.01  fof(f49,plain,(
% 1.72/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.01    inference(cnf_transformation,[],[f29])).
% 1.72/1.01  
% 1.72/1.01  fof(f11,conjecture,(
% 1.72/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.72/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.01  
% 1.72/1.01  fof(f12,negated_conjecture,(
% 1.72/1.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.72/1.01    inference(negated_conjecture,[],[f11])).
% 1.72/1.01  
% 1.72/1.01  fof(f21,plain,(
% 1.72/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.72/1.01    inference(ennf_transformation,[],[f12])).
% 1.72/1.01  
% 1.72/1.01  fof(f22,plain,(
% 1.72/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.72/1.01    inference(flattening,[],[f21])).
% 1.72/1.01  
% 1.72/1.01  fof(f30,plain,(
% 1.72/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.72/1.01    introduced(choice_axiom,[])).
% 1.72/1.01  
% 1.72/1.01  fof(f31,plain,(
% 1.72/1.01    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.72/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f30])).
% 1.72/1.01  
% 1.72/1.01  fof(f55,plain,(
% 1.72/1.01    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 1.72/1.01    inference(cnf_transformation,[],[f31])).
% 1.72/1.01  
% 1.72/1.01  fof(f54,plain,(
% 1.72/1.01    v1_funct_1(sK0)),
% 1.72/1.01    inference(cnf_transformation,[],[f31])).
% 1.72/1.01  
% 1.72/1.01  fof(f9,axiom,(
% 1.72/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.72/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.01  
% 1.72/1.01  fof(f18,plain,(
% 1.72/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/1.01    inference(ennf_transformation,[],[f9])).
% 1.72/1.01  
% 1.72/1.01  fof(f46,plain,(
% 1.72/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.01    inference(cnf_transformation,[],[f18])).
% 1.72/1.01  
% 1.72/1.01  fof(f6,axiom,(
% 1.72/1.01    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.72/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.01  
% 1.72/1.01  fof(f15,plain,(
% 1.72/1.01    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.72/1.01    inference(ennf_transformation,[],[f6])).
% 1.72/1.01  
% 1.72/1.01  fof(f43,plain,(
% 1.72/1.01    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.72/1.01    inference(cnf_transformation,[],[f15])).
% 1.72/1.01  
% 1.72/1.01  fof(f53,plain,(
% 1.72/1.01    v1_relat_1(sK0)),
% 1.72/1.01    inference(cnf_transformation,[],[f31])).
% 1.72/1.01  
% 1.72/1.01  fof(f4,axiom,(
% 1.72/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.72/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.01  
% 1.72/1.01  fof(f27,plain,(
% 1.72/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.72/1.01    inference(nnf_transformation,[],[f4])).
% 1.72/1.01  
% 1.72/1.01  fof(f40,plain,(
% 1.72/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.72/1.01    inference(cnf_transformation,[],[f27])).
% 1.72/1.01  
% 1.72/1.01  fof(f3,axiom,(
% 1.72/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.72/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.01  
% 1.72/1.01  fof(f25,plain,(
% 1.72/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.72/1.01    inference(nnf_transformation,[],[f3])).
% 1.72/1.01  
% 1.72/1.01  fof(f26,plain,(
% 1.72/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.72/1.01    inference(flattening,[],[f25])).
% 1.72/1.01  
% 1.72/1.01  fof(f38,plain,(
% 1.72/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.72/1.01    inference(cnf_transformation,[],[f26])).
% 1.72/1.01  
% 1.72/1.01  fof(f58,plain,(
% 1.72/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.72/1.01    inference(equality_resolution,[],[f38])).
% 1.72/1.01  
% 1.72/1.01  fof(f50,plain,(
% 1.72/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.01    inference(cnf_transformation,[],[f29])).
% 1.72/1.01  
% 1.72/1.01  fof(f63,plain,(
% 1.72/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.72/1.01    inference(equality_resolution,[],[f50])).
% 1.72/1.01  
% 1.72/1.01  fof(f37,plain,(
% 1.72/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.72/1.01    inference(cnf_transformation,[],[f26])).
% 1.72/1.01  
% 1.72/1.01  fof(f59,plain,(
% 1.72/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.72/1.01    inference(equality_resolution,[],[f37])).
% 1.72/1.01  
% 1.72/1.01  fof(f2,axiom,(
% 1.72/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.72/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.01  
% 1.72/1.01  fof(f35,plain,(
% 1.72/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.72/1.01    inference(cnf_transformation,[],[f2])).
% 1.72/1.01  
% 1.72/1.01  fof(f1,axiom,(
% 1.72/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.72/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.72/1.01  
% 1.72/1.01  fof(f23,plain,(
% 1.72/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/1.01    inference(nnf_transformation,[],[f1])).
% 1.72/1.01  
% 1.72/1.01  fof(f24,plain,(
% 1.72/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/1.01    inference(flattening,[],[f23])).
% 1.72/1.01  
% 1.72/1.01  fof(f34,plain,(
% 1.72/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.72/1.01    inference(cnf_transformation,[],[f24])).
% 1.72/1.01  
% 1.72/1.01  fof(f52,plain,(
% 1.72/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.01    inference(cnf_transformation,[],[f29])).
% 1.72/1.01  
% 1.72/1.01  fof(f60,plain,(
% 1.72/1.01    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/1.01    inference(equality_resolution,[],[f52])).
% 1.72/1.01  
% 1.72/1.01  fof(f61,plain,(
% 1.72/1.01    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.72/1.01    inference(equality_resolution,[],[f60])).
% 1.72/1.01  
% 1.72/1.01  cnf(c_18,plain,
% 1.72/1.01      ( v1_funct_2(X0,X1,X2)
% 1.72/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.01      | k1_relset_1(X1,X2,X0) != X1
% 1.72/1.01      | k1_xboole_0 = X2 ),
% 1.72/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_21,negated_conjecture,
% 1.72/1.01      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 1.72/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | ~ v1_funct_1(sK0) ),
% 1.72/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_22,negated_conjecture,
% 1.72/1.01      ( v1_funct_1(sK0) ),
% 1.72/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_124,plain,
% 1.72/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 1.72/1.01      inference(global_propositional_subsumption,
% 1.72/1.01                [status(thm)],
% 1.72/1.01                [c_21,c_22]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_125,negated_conjecture,
% 1.72/1.01      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 1.72/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
% 1.72/1.01      inference(renaming,[status(thm)],[c_124]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_598,plain,
% 1.72/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | k1_relset_1(X1,X2,X0) != X1
% 1.72/1.01      | k2_relat_1(sK0) != X2
% 1.72/1.01      | k1_relat_1(sK0) != X1
% 1.72/1.01      | sK0 != X0
% 1.72/1.01      | k1_xboole_0 = X2 ),
% 1.72/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_125]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_599,plain,
% 1.72/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
% 1.72/1.01      | k1_xboole_0 = k2_relat_1(sK0) ),
% 1.72/1.01      inference(unflattening,[status(thm)],[c_598]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_14,plain,
% 1.72/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.72/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.72/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_607,plain,
% 1.72/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | k1_xboole_0 = k2_relat_1(sK0) ),
% 1.72/1.01      inference(forward_subsumption_resolution,
% 1.72/1.01                [status(thm)],
% 1.72/1.01                [c_599,c_14]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1138,plain,
% 1.72/1.01      ( k1_xboole_0 = k2_relat_1(sK0)
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_11,plain,
% 1.72/1.01      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 1.72/1.01      | ~ v1_relat_1(X0) ),
% 1.72/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_23,negated_conjecture,
% 1.72/1.01      ( v1_relat_1(sK0) ),
% 1.72/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_323,plain,
% 1.72/1.01      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 1.72/1.01      | sK0 != X0 ),
% 1.72/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_324,plain,
% 1.72/1.01      ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
% 1.72/1.01      inference(unflattening,[status(thm)],[c_323]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_7,plain,
% 1.72/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.72/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1250,plain,
% 1.72/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
% 1.72/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1259,plain,
% 1.72/1.01      ( k1_xboole_0 = k2_relat_1(sK0) ),
% 1.72/1.01      inference(global_propositional_subsumption,
% 1.72/1.01                [status(thm)],
% 1.72/1.01                [c_1138,c_324,c_607,c_1250]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1145,plain,
% 1.72/1.01      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 1.72/1.01      | v1_relat_1(X0) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1803,plain,
% 1.72/1.01      ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) = iProver_top
% 1.72/1.01      | v1_relat_1(sK0) != iProver_top ),
% 1.72/1.01      inference(superposition,[status(thm)],[c_1259,c_1145]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_4,plain,
% 1.72/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.72/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1807,plain,
% 1.72/1.01      ( r1_tarski(sK0,k1_xboole_0) = iProver_top
% 1.72/1.01      | v1_relat_1(sK0) != iProver_top ),
% 1.72/1.01      inference(demodulation,[status(thm)],[c_1803,c_4]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_24,plain,
% 1.72/1.01      ( v1_relat_1(sK0) = iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1912,plain,
% 1.72/1.01      ( r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 1.72/1.01      inference(global_propositional_subsumption,
% 1.72/1.01                [status(thm)],
% 1.72/1.01                [c_1807,c_24]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1147,plain,
% 1.72/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.72/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1143,plain,
% 1.72/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.72/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_2003,plain,
% 1.72/1.01      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 1.72/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.72/1.01      inference(superposition,[status(thm)],[c_4,c_1143]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_2124,plain,
% 1.72/1.01      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 1.72/1.01      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 1.72/1.01      inference(superposition,[status(thm)],[c_1147,c_2003]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_2317,plain,
% 1.72/1.01      ( k1_relset_1(X0,k1_xboole_0,sK0) = k1_relat_1(sK0) ),
% 1.72/1.01      inference(superposition,[status(thm)],[c_1912,c_2124]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_17,plain,
% 1.72/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.72/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.72/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.72/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_582,plain,
% 1.72/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.72/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.72/1.01      | k2_relat_1(sK0) != X1
% 1.72/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | sK0 != X0 ),
% 1.72/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_125]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_583,plain,
% 1.72/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
% 1.72/1.01      | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) != k1_xboole_0 ),
% 1.72/1.01      inference(unflattening,[status(thm)],[c_582]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1139,plain,
% 1.72/1.01      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_5,plain,
% 1.72/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.72/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1201,plain,
% 1.72/1.01      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.72/1.01      inference(demodulation,[status(thm)],[c_1139,c_5]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_325,plain,
% 1.72/1.01      ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) = iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1251,plain,
% 1.72/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) = iProver_top
% 1.72/1.01      | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1280,plain,
% 1.72/1.01      ( k1_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.72/1.01      inference(global_propositional_subsumption,
% 1.72/1.01                [status(thm)],
% 1.72/1.01                [c_1201,c_325,c_1251]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1281,plain,
% 1.72/1.01      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.72/1.01      inference(renaming,[status(thm)],[c_1280]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1284,plain,
% 1.72/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.72/1.01      inference(light_normalisation,[status(thm)],[c_1281,c_1259]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_2368,plain,
% 1.72/1.01      ( k1_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.72/1.01      inference(demodulation,[status(thm)],[c_2317,c_1284]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1392,plain,
% 1.72/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
% 1.72/1.01      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 1.72/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1393,plain,
% 1.72/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.72/1.01      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_3,plain,
% 1.72/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 1.72/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1381,plain,
% 1.72/1.01      ( r1_tarski(k1_xboole_0,sK0) ),
% 1.72/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1384,plain,
% 1.72/1.01      ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_0,plain,
% 1.72/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.72/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1296,plain,
% 1.72/1.01      ( ~ r1_tarski(sK0,k1_xboole_0)
% 1.72/1.01      | ~ r1_tarski(k1_xboole_0,sK0)
% 1.72/1.01      | sK0 = k1_xboole_0 ),
% 1.72/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1297,plain,
% 1.72/1.01      ( sK0 = k1_xboole_0
% 1.72/1.01      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 1.72/1.01      | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_15,plain,
% 1.72/1.01      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 1.72/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 1.72/1.01      | k1_xboole_0 = X0 ),
% 1.72/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_555,plain,
% 1.72/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 1.72/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) != X0
% 1.72/1.01      | sK0 != k1_xboole_0
% 1.72/1.01      | k1_xboole_0 = X0 ),
% 1.72/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_125]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_556,plain,
% 1.72/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
% 1.72/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | sK0 != k1_xboole_0
% 1.72/1.01      | k1_xboole_0 = k1_relat_1(sK0) ),
% 1.72/1.01      inference(unflattening,[status(thm)],[c_555]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1140,plain,
% 1.72/1.01      ( k2_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | sK0 != k1_xboole_0
% 1.72/1.01      | k1_xboole_0 = k1_relat_1(sK0)
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 1.72/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
% 1.72/1.01      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1210,plain,
% 1.72/1.01      ( k2_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) = k1_xboole_0
% 1.72/1.01      | sK0 != k1_xboole_0
% 1.72/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 1.72/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.72/1.01      inference(demodulation,[status(thm)],[c_1140,c_4]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_67,plain,
% 1.72/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 1.72/1.01      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 1.72/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_72,plain,
% 1.72/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 1.72/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1226,plain,
% 1.72/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 1.72/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 1.72/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) = k1_xboole_0
% 1.72/1.01      | sK0 != k1_xboole_0 ),
% 1.72/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1210]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1290,plain,
% 1.72/1.01      ( k2_relat_1(sK0) != k1_xboole_0
% 1.72/1.01      | k1_relat_1(sK0) = k1_xboole_0
% 1.72/1.01      | sK0 != k1_xboole_0 ),
% 1.72/1.01      inference(global_propositional_subsumption,
% 1.72/1.01                [status(thm)],
% 1.72/1.01                [c_1210,c_67,c_72,c_324,c_1226,c_1250]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1292,plain,
% 1.72/1.01      ( k1_relat_1(sK0) = k1_xboole_0
% 1.72/1.01      | sK0 != k1_xboole_0
% 1.72/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 1.72/1.01      inference(light_normalisation,[status(thm)],[c_1290,c_1259]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(c_1293,plain,
% 1.72/1.01      ( k1_relat_1(sK0) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 1.72/1.01      inference(equality_resolution_simp,[status(thm)],[c_1292]) ).
% 1.72/1.01  
% 1.72/1.01  cnf(contradiction,plain,
% 1.72/1.01      ( $false ),
% 1.72/1.01      inference(minisat,
% 1.72/1.01                [status(thm)],
% 1.72/1.01                [c_2368,c_1807,c_1393,c_1384,c_1297,c_1293,c_24]) ).
% 1.72/1.01  
% 1.72/1.01  
% 1.72/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.72/1.01  
% 1.72/1.01  ------                               Statistics
% 1.72/1.01  
% 1.72/1.01  ------ General
% 1.72/1.01  
% 1.72/1.01  abstr_ref_over_cycles:                  0
% 1.72/1.01  abstr_ref_under_cycles:                 0
% 1.72/1.01  gc_basic_clause_elim:                   0
% 1.72/1.01  forced_gc_time:                         0
% 1.72/1.01  parsing_time:                           0.01
% 1.72/1.01  unif_index_cands_time:                  0.
% 1.72/1.01  unif_index_add_time:                    0.
% 1.72/1.01  orderings_time:                         0.
% 1.72/1.01  out_proof_time:                         0.009
% 1.72/1.01  total_time:                             0.097
% 1.72/1.01  num_of_symbols:                         44
% 1.72/1.01  num_of_terms:                           1777
% 1.72/1.01  
% 1.72/1.01  ------ Preprocessing
% 1.72/1.01  
% 1.72/1.01  num_of_splits:                          0
% 1.72/1.01  num_of_split_atoms:                     0
% 1.72/1.01  num_of_reused_defs:                     0
% 1.72/1.01  num_eq_ax_congr_red:                    4
% 1.72/1.01  num_of_sem_filtered_clauses:            2
% 1.72/1.01  num_of_subtypes:                        0
% 1.72/1.01  monotx_restored_types:                  0
% 1.72/1.01  sat_num_of_epr_types:                   0
% 1.72/1.01  sat_num_of_non_cyclic_types:            0
% 1.72/1.01  sat_guarded_non_collapsed_types:        0
% 1.72/1.01  num_pure_diseq_elim:                    0
% 1.72/1.01  simp_replaced_by:                       0
% 1.72/1.01  res_preprocessed:                       92
% 1.72/1.01  prep_upred:                             0
% 1.72/1.01  prep_unflattend:                        38
% 1.72/1.01  smt_new_axioms:                         0
% 1.72/1.01  pred_elim_cands:                        3
% 1.72/1.01  pred_elim:                              2
% 1.72/1.01  pred_elim_cl:                           6
% 1.72/1.01  pred_elim_cycles:                       6
% 1.72/1.01  merged_defs:                            8
% 1.72/1.01  merged_defs_ncl:                        0
% 1.72/1.01  bin_hyper_res:                          8
% 1.72/1.01  prep_cycles:                            4
% 1.72/1.01  pred_elim_time:                         0.006
% 1.72/1.01  splitting_time:                         0.
% 1.72/1.01  sem_filter_time:                        0.
% 1.72/1.01  monotx_time:                            0.
% 1.72/1.01  subtype_inf_time:                       0.
% 1.72/1.01  
% 1.72/1.01  ------ Problem properties
% 1.72/1.01  
% 1.72/1.01  clauses:                                16
% 1.72/1.01  conjectures:                            1
% 1.72/1.01  epr:                                    4
% 1.72/1.01  horn:                                   15
% 1.72/1.01  ground:                                 4
% 1.72/1.01  unary:                                  5
% 1.72/1.01  binary:                                 7
% 1.72/1.01  lits:                                   34
% 1.72/1.01  lits_eq:                                13
% 1.72/1.01  fd_pure:                                0
% 1.72/1.01  fd_pseudo:                              0
% 1.72/1.01  fd_cond:                                1
% 1.72/1.01  fd_pseudo_cond:                         1
% 1.72/1.01  ac_symbols:                             0
% 1.72/1.01  
% 1.72/1.01  ------ Propositional Solver
% 1.72/1.01  
% 1.72/1.01  prop_solver_calls:                      28
% 1.72/1.01  prop_fast_solver_calls:                 561
% 1.72/1.01  smt_solver_calls:                       0
% 1.72/1.01  smt_fast_solver_calls:                  0
% 1.72/1.01  prop_num_of_clauses:                    735
% 1.72/1.01  prop_preprocess_simplified:             3206
% 1.72/1.01  prop_fo_subsumed:                       7
% 1.72/1.01  prop_solver_time:                       0.
% 1.72/1.01  smt_solver_time:                        0.
% 1.72/1.01  smt_fast_solver_time:                   0.
% 1.72/1.01  prop_fast_solver_time:                  0.
% 1.72/1.01  prop_unsat_core_time:                   0.
% 1.72/1.01  
% 1.72/1.01  ------ QBF
% 1.72/1.01  
% 1.72/1.01  qbf_q_res:                              0
% 1.72/1.01  qbf_num_tautologies:                    0
% 1.72/1.01  qbf_prep_cycles:                        0
% 1.72/1.01  
% 1.72/1.01  ------ BMC1
% 1.72/1.01  
% 1.72/1.01  bmc1_current_bound:                     -1
% 1.72/1.01  bmc1_last_solved_bound:                 -1
% 1.72/1.01  bmc1_unsat_core_size:                   -1
% 1.72/1.01  bmc1_unsat_core_parents_size:           -1
% 1.72/1.01  bmc1_merge_next_fun:                    0
% 1.72/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.72/1.01  
% 1.72/1.01  ------ Instantiation
% 1.72/1.01  
% 1.72/1.01  inst_num_of_clauses:                    244
% 1.72/1.01  inst_num_in_passive:                    119
% 1.72/1.01  inst_num_in_active:                     113
% 1.72/1.01  inst_num_in_unprocessed:                12
% 1.72/1.01  inst_num_of_loops:                      160
% 1.72/1.01  inst_num_of_learning_restarts:          0
% 1.72/1.01  inst_num_moves_active_passive:          44
% 1.72/1.01  inst_lit_activity:                      0
% 1.72/1.01  inst_lit_activity_moves:                0
% 1.72/1.01  inst_num_tautologies:                   0
% 1.72/1.01  inst_num_prop_implied:                  0
% 1.72/1.01  inst_num_existing_simplified:           0
% 1.72/1.01  inst_num_eq_res_simplified:             0
% 1.72/1.01  inst_num_child_elim:                    0
% 1.72/1.01  inst_num_of_dismatching_blockings:      29
% 1.72/1.01  inst_num_of_non_proper_insts:           239
% 1.72/1.01  inst_num_of_duplicates:                 0
% 1.72/1.01  inst_inst_num_from_inst_to_res:         0
% 1.72/1.01  inst_dismatching_checking_time:         0.
% 1.72/1.01  
% 1.72/1.01  ------ Resolution
% 1.72/1.01  
% 1.72/1.01  res_num_of_clauses:                     0
% 1.72/1.01  res_num_in_passive:                     0
% 1.72/1.01  res_num_in_active:                      0
% 1.72/1.01  res_num_of_loops:                       96
% 1.72/1.01  res_forward_subset_subsumed:            23
% 1.72/1.01  res_backward_subset_subsumed:           0
% 1.72/1.01  res_forward_subsumed:                   0
% 1.72/1.01  res_backward_subsumed:                  0
% 1.72/1.01  res_forward_subsumption_resolution:     2
% 1.72/1.01  res_backward_subsumption_resolution:    0
% 1.72/1.01  res_clause_to_clause_subsumption:       148
% 1.72/1.01  res_orphan_elimination:                 0
% 1.72/1.01  res_tautology_del:                      38
% 1.72/1.01  res_num_eq_res_simplified:              0
% 1.72/1.01  res_num_sel_changes:                    0
% 1.72/1.01  res_moves_from_active_to_pass:          0
% 1.72/1.01  
% 1.72/1.01  ------ Superposition
% 1.72/1.01  
% 1.72/1.01  sup_time_total:                         0.
% 1.72/1.01  sup_time_generating:                    0.
% 1.72/1.01  sup_time_sim_full:                      0.
% 1.72/1.01  sup_time_sim_immed:                     0.
% 1.72/1.01  
% 1.72/1.01  sup_num_of_clauses:                     39
% 1.72/1.01  sup_num_in_active:                      29
% 1.72/1.01  sup_num_in_passive:                     10
% 1.72/1.01  sup_num_of_loops:                       30
% 1.72/1.01  sup_fw_superposition:                   32
% 1.72/1.01  sup_bw_superposition:                   5
% 1.72/1.01  sup_immediate_simplified:               2
% 1.72/1.01  sup_given_eliminated:                   0
% 1.72/1.01  comparisons_done:                       0
% 1.72/1.01  comparisons_avoided:                    0
% 1.72/1.01  
% 1.72/1.01  ------ Simplifications
% 1.72/1.01  
% 1.72/1.01  
% 1.72/1.01  sim_fw_subset_subsumed:                 0
% 1.72/1.01  sim_bw_subset_subsumed:                 0
% 1.72/1.01  sim_fw_subsumed:                        0
% 1.72/1.01  sim_bw_subsumed:                        1
% 1.72/1.01  sim_fw_subsumption_res:                 0
% 1.72/1.01  sim_bw_subsumption_res:                 0
% 1.72/1.01  sim_tautology_del:                      2
% 1.72/1.01  sim_eq_tautology_del:                   1
% 1.72/1.01  sim_eq_res_simp:                        1
% 1.72/1.01  sim_fw_demodulated:                     3
% 1.72/1.01  sim_bw_demodulated:                     1
% 1.72/1.01  sim_light_normalised:                   2
% 1.72/1.01  sim_joinable_taut:                      0
% 1.72/1.01  sim_joinable_simp:                      0
% 1.72/1.01  sim_ac_normalised:                      0
% 1.72/1.01  sim_smt_subsumption:                    0
% 1.72/1.01  
%------------------------------------------------------------------------------
