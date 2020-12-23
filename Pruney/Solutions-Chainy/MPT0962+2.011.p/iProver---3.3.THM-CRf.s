%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:10 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 373 expanded)
%              Number of clauses        :   49 ( 129 expanded)
%              Number of leaves         :   11 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  283 (1704 expanded)
%              Number of equality atoms :  101 ( 328 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
        | ~ v1_funct_1(sK2) )
      & r1_tarski(k2_relat_1(sK2),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
      | ~ v1_funct_1(sK2) )
    & r1_tarski(k2_relat_1(sK2),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f39])).

fof(f76,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_26,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_175,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_34])).

cnf(c_176,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_798,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK2) != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_176])).

cnf(c_799,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_798])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_807,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_xboole_0 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_799,c_21])).

cnf(c_2247,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_3107,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_2247])).

cnf(c_35,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2635,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2571,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k1_relat_1(sK2),X0)
    | ~ r1_tarski(k2_relat_1(sK2),X1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2634,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2571])).

cnf(c_2747,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2634])).

cnf(c_1626,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2588,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1626])).

cnf(c_2841,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2588])).

cnf(c_1625,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2842,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_3196,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3107,c_35,c_33,c_807,c_2635,c_2747,c_2841,c_2842])).

cnf(c_2256,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3203,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3196,c_2256])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2271,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4082,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3203,c_2271])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_811,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | k2_relat_1(X0) != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_176])).

cnf(c_812,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != sK1 ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_814,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_35,c_34])).

cnf(c_2590,plain,
    ( k2_relat_1(sK2) != X0
    | k2_relat_1(sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1626])).

cnf(c_2591,plain,
    ( k2_relat_1(sK2) = sK1
    | k2_relat_1(sK2) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_2655,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_3245,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | k2_relat_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3246,plain,
    ( k2_relat_1(sK2) = X0
    | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3245])).

cnf(c_3248,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3246])).

cnf(c_4345,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4082,c_35,c_33,c_807,c_814,c_2591,c_2635,c_2655,c_2747,c_2841,c_2842,c_3203,c_3248])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2269,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3075,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_2267])).

cnf(c_4350,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4345,c_3075])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.14/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.00  
% 2.14/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.14/1.00  
% 2.14/1.00  ------  iProver source info
% 2.14/1.00  
% 2.14/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.14/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.14/1.00  git: non_committed_changes: false
% 2.14/1.00  git: last_make_outside_of_git: false
% 2.14/1.00  
% 2.14/1.00  ------ 
% 2.14/1.00  
% 2.14/1.00  ------ Input Options
% 2.14/1.00  
% 2.14/1.00  --out_options                           all
% 2.14/1.00  --tptp_safe_out                         true
% 2.14/1.00  --problem_path                          ""
% 2.14/1.00  --include_path                          ""
% 2.14/1.00  --clausifier                            res/vclausify_rel
% 2.14/1.00  --clausifier_options                    --mode clausify
% 2.14/1.00  --stdin                                 false
% 2.14/1.00  --stats_out                             all
% 2.14/1.00  
% 2.14/1.00  ------ General Options
% 2.14/1.00  
% 2.14/1.00  --fof                                   false
% 2.14/1.00  --time_out_real                         305.
% 2.14/1.00  --time_out_virtual                      -1.
% 2.14/1.00  --symbol_type_check                     false
% 2.14/1.00  --clausify_out                          false
% 2.14/1.00  --sig_cnt_out                           false
% 2.14/1.00  --trig_cnt_out                          false
% 2.14/1.00  --trig_cnt_out_tolerance                1.
% 2.14/1.00  --trig_cnt_out_sk_spl                   false
% 2.14/1.00  --abstr_cl_out                          false
% 2.14/1.00  
% 2.14/1.00  ------ Global Options
% 2.14/1.00  
% 2.14/1.00  --schedule                              default
% 2.14/1.00  --add_important_lit                     false
% 2.14/1.00  --prop_solver_per_cl                    1000
% 2.14/1.00  --min_unsat_core                        false
% 2.14/1.00  --soft_assumptions                      false
% 2.14/1.00  --soft_lemma_size                       3
% 2.14/1.00  --prop_impl_unit_size                   0
% 2.14/1.00  --prop_impl_unit                        []
% 2.14/1.00  --share_sel_clauses                     true
% 2.14/1.00  --reset_solvers                         false
% 2.14/1.00  --bc_imp_inh                            [conj_cone]
% 2.14/1.00  --conj_cone_tolerance                   3.
% 2.14/1.00  --extra_neg_conj                        none
% 2.14/1.00  --large_theory_mode                     true
% 2.14/1.00  --prolific_symb_bound                   200
% 2.14/1.00  --lt_threshold                          2000
% 2.14/1.00  --clause_weak_htbl                      true
% 2.14/1.00  --gc_record_bc_elim                     false
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing Options
% 2.14/1.00  
% 2.14/1.00  --preprocessing_flag                    true
% 2.14/1.00  --time_out_prep_mult                    0.1
% 2.14/1.00  --splitting_mode                        input
% 2.14/1.00  --splitting_grd                         true
% 2.14/1.00  --splitting_cvd                         false
% 2.14/1.00  --splitting_cvd_svl                     false
% 2.14/1.00  --splitting_nvd                         32
% 2.14/1.00  --sub_typing                            true
% 2.14/1.00  --prep_gs_sim                           true
% 2.14/1.00  --prep_unflatten                        true
% 2.14/1.00  --prep_res_sim                          true
% 2.14/1.00  --prep_upred                            true
% 2.14/1.00  --prep_sem_filter                       exhaustive
% 2.14/1.00  --prep_sem_filter_out                   false
% 2.14/1.00  --pred_elim                             true
% 2.14/1.00  --res_sim_input                         true
% 2.14/1.00  --eq_ax_congr_red                       true
% 2.14/1.00  --pure_diseq_elim                       true
% 2.14/1.00  --brand_transform                       false
% 2.14/1.00  --non_eq_to_eq                          false
% 2.14/1.00  --prep_def_merge                        true
% 2.14/1.00  --prep_def_merge_prop_impl              false
% 2.14/1.00  --prep_def_merge_mbd                    true
% 2.14/1.00  --prep_def_merge_tr_red                 false
% 2.14/1.00  --prep_def_merge_tr_cl                  false
% 2.14/1.00  --smt_preprocessing                     true
% 2.14/1.00  --smt_ac_axioms                         fast
% 2.14/1.00  --preprocessed_out                      false
% 2.14/1.00  --preprocessed_stats                    false
% 2.14/1.00  
% 2.14/1.00  ------ Abstraction refinement Options
% 2.14/1.00  
% 2.14/1.00  --abstr_ref                             []
% 2.14/1.00  --abstr_ref_prep                        false
% 2.14/1.00  --abstr_ref_until_sat                   false
% 2.14/1.00  --abstr_ref_sig_restrict                funpre
% 2.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/1.00  --abstr_ref_under                       []
% 2.14/1.00  
% 2.14/1.00  ------ SAT Options
% 2.14/1.00  
% 2.14/1.00  --sat_mode                              false
% 2.14/1.00  --sat_fm_restart_options                ""
% 2.14/1.00  --sat_gr_def                            false
% 2.14/1.00  --sat_epr_types                         true
% 2.14/1.00  --sat_non_cyclic_types                  false
% 2.14/1.00  --sat_finite_models                     false
% 2.14/1.00  --sat_fm_lemmas                         false
% 2.14/1.00  --sat_fm_prep                           false
% 2.14/1.00  --sat_fm_uc_incr                        true
% 2.14/1.00  --sat_out_model                         small
% 2.14/1.00  --sat_out_clauses                       false
% 2.14/1.00  
% 2.14/1.00  ------ QBF Options
% 2.14/1.00  
% 2.14/1.00  --qbf_mode                              false
% 2.14/1.00  --qbf_elim_univ                         false
% 2.14/1.00  --qbf_dom_inst                          none
% 2.14/1.00  --qbf_dom_pre_inst                      false
% 2.14/1.00  --qbf_sk_in                             false
% 2.14/1.00  --qbf_pred_elim                         true
% 2.14/1.00  --qbf_split                             512
% 2.14/1.00  
% 2.14/1.00  ------ BMC1 Options
% 2.14/1.00  
% 2.14/1.00  --bmc1_incremental                      false
% 2.14/1.00  --bmc1_axioms                           reachable_all
% 2.14/1.00  --bmc1_min_bound                        0
% 2.14/1.00  --bmc1_max_bound                        -1
% 2.14/1.00  --bmc1_max_bound_default                -1
% 2.14/1.00  --bmc1_symbol_reachability              true
% 2.14/1.00  --bmc1_property_lemmas                  false
% 2.14/1.00  --bmc1_k_induction                      false
% 2.14/1.00  --bmc1_non_equiv_states                 false
% 2.14/1.00  --bmc1_deadlock                         false
% 2.14/1.00  --bmc1_ucm                              false
% 2.14/1.00  --bmc1_add_unsat_core                   none
% 2.14/1.00  --bmc1_unsat_core_children              false
% 2.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/1.00  --bmc1_out_stat                         full
% 2.14/1.00  --bmc1_ground_init                      false
% 2.14/1.00  --bmc1_pre_inst_next_state              false
% 2.14/1.00  --bmc1_pre_inst_state                   false
% 2.14/1.00  --bmc1_pre_inst_reach_state             false
% 2.14/1.00  --bmc1_out_unsat_core                   false
% 2.14/1.00  --bmc1_aig_witness_out                  false
% 2.14/1.00  --bmc1_verbose                          false
% 2.14/1.00  --bmc1_dump_clauses_tptp                false
% 2.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.14/1.00  --bmc1_dump_file                        -
% 2.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.14/1.00  --bmc1_ucm_extend_mode                  1
% 2.14/1.00  --bmc1_ucm_init_mode                    2
% 2.14/1.00  --bmc1_ucm_cone_mode                    none
% 2.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.14/1.00  --bmc1_ucm_relax_model                  4
% 2.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/1.00  --bmc1_ucm_layered_model                none
% 2.14/1.00  --bmc1_ucm_max_lemma_size               10
% 2.14/1.00  
% 2.14/1.00  ------ AIG Options
% 2.14/1.00  
% 2.14/1.00  --aig_mode                              false
% 2.14/1.00  
% 2.14/1.00  ------ Instantiation Options
% 2.14/1.00  
% 2.14/1.00  --instantiation_flag                    true
% 2.14/1.00  --inst_sos_flag                         false
% 2.14/1.00  --inst_sos_phase                        true
% 2.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/1.00  --inst_lit_sel_side                     num_symb
% 2.14/1.00  --inst_solver_per_active                1400
% 2.14/1.00  --inst_solver_calls_frac                1.
% 2.14/1.00  --inst_passive_queue_type               priority_queues
% 2.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/1.00  --inst_passive_queues_freq              [25;2]
% 2.14/1.00  --inst_dismatching                      true
% 2.14/1.00  --inst_eager_unprocessed_to_passive     true
% 2.14/1.00  --inst_prop_sim_given                   true
% 2.14/1.00  --inst_prop_sim_new                     false
% 2.14/1.00  --inst_subs_new                         false
% 2.14/1.00  --inst_eq_res_simp                      false
% 2.14/1.00  --inst_subs_given                       false
% 2.14/1.00  --inst_orphan_elimination               true
% 2.14/1.00  --inst_learning_loop_flag               true
% 2.14/1.00  --inst_learning_start                   3000
% 2.14/1.00  --inst_learning_factor                  2
% 2.14/1.00  --inst_start_prop_sim_after_learn       3
% 2.14/1.00  --inst_sel_renew                        solver
% 2.14/1.00  --inst_lit_activity_flag                true
% 2.14/1.00  --inst_restr_to_given                   false
% 2.14/1.00  --inst_activity_threshold               500
% 2.14/1.00  --inst_out_proof                        true
% 2.14/1.00  
% 2.14/1.00  ------ Resolution Options
% 2.14/1.00  
% 2.14/1.00  --resolution_flag                       true
% 2.14/1.00  --res_lit_sel                           adaptive
% 2.14/1.00  --res_lit_sel_side                      none
% 2.14/1.00  --res_ordering                          kbo
% 2.14/1.00  --res_to_prop_solver                    active
% 2.14/1.00  --res_prop_simpl_new                    false
% 2.14/1.00  --res_prop_simpl_given                  true
% 2.14/1.00  --res_passive_queue_type                priority_queues
% 2.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/1.00  --res_passive_queues_freq               [15;5]
% 2.14/1.00  --res_forward_subs                      full
% 2.14/1.00  --res_backward_subs                     full
% 2.14/1.00  --res_forward_subs_resolution           true
% 2.14/1.00  --res_backward_subs_resolution          true
% 2.14/1.00  --res_orphan_elimination                true
% 2.14/1.00  --res_time_limit                        2.
% 2.14/1.00  --res_out_proof                         true
% 2.14/1.00  
% 2.14/1.00  ------ Superposition Options
% 2.14/1.00  
% 2.14/1.00  --superposition_flag                    true
% 2.14/1.00  --sup_passive_queue_type                priority_queues
% 2.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.14/1.00  --demod_completeness_check              fast
% 2.14/1.00  --demod_use_ground                      true
% 2.14/1.00  --sup_to_prop_solver                    passive
% 2.14/1.00  --sup_prop_simpl_new                    true
% 2.14/1.00  --sup_prop_simpl_given                  true
% 2.14/1.00  --sup_fun_splitting                     false
% 2.14/1.00  --sup_smt_interval                      50000
% 2.14/1.00  
% 2.14/1.00  ------ Superposition Simplification Setup
% 2.14/1.00  
% 2.14/1.00  --sup_indices_passive                   []
% 2.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_full_bw                           [BwDemod]
% 2.14/1.00  --sup_immed_triv                        [TrivRules]
% 2.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_immed_bw_main                     []
% 2.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.00  
% 2.14/1.00  ------ Combination Options
% 2.14/1.00  
% 2.14/1.00  --comb_res_mult                         3
% 2.14/1.00  --comb_sup_mult                         2
% 2.14/1.00  --comb_inst_mult                        10
% 2.14/1.00  
% 2.14/1.00  ------ Debug Options
% 2.14/1.00  
% 2.14/1.00  --dbg_backtrace                         false
% 2.14/1.00  --dbg_dump_prop_clauses                 false
% 2.14/1.00  --dbg_dump_prop_clauses_file            -
% 2.14/1.00  --dbg_out_stat                          false
% 2.14/1.00  ------ Parsing...
% 2.14/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.14/1.00  ------ Proving...
% 2.14/1.00  ------ Problem Properties 
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  clauses                                 33
% 2.14/1.00  conjectures                             3
% 2.14/1.00  EPR                                     5
% 2.14/1.00  Horn                                    26
% 2.14/1.00  unary                                   13
% 2.14/1.00  binary                                  10
% 2.14/1.00  lits                                    71
% 2.14/1.00  lits eq                                 29
% 2.14/1.00  fd_pure                                 0
% 2.14/1.00  fd_pseudo                               0
% 2.14/1.00  fd_cond                                 5
% 2.14/1.00  fd_pseudo_cond                          1
% 2.14/1.00  AC symbols                              0
% 2.14/1.00  
% 2.14/1.00  ------ Schedule dynamic 5 is on 
% 2.14/1.00  
% 2.14/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  ------ 
% 2.14/1.00  Current options:
% 2.14/1.00  ------ 
% 2.14/1.00  
% 2.14/1.00  ------ Input Options
% 2.14/1.00  
% 2.14/1.00  --out_options                           all
% 2.14/1.00  --tptp_safe_out                         true
% 2.14/1.00  --problem_path                          ""
% 2.14/1.00  --include_path                          ""
% 2.14/1.00  --clausifier                            res/vclausify_rel
% 2.14/1.00  --clausifier_options                    --mode clausify
% 2.14/1.00  --stdin                                 false
% 2.14/1.00  --stats_out                             all
% 2.14/1.00  
% 2.14/1.00  ------ General Options
% 2.14/1.00  
% 2.14/1.00  --fof                                   false
% 2.14/1.00  --time_out_real                         305.
% 2.14/1.00  --time_out_virtual                      -1.
% 2.14/1.00  --symbol_type_check                     false
% 2.14/1.00  --clausify_out                          false
% 2.14/1.00  --sig_cnt_out                           false
% 2.14/1.00  --trig_cnt_out                          false
% 2.14/1.00  --trig_cnt_out_tolerance                1.
% 2.14/1.00  --trig_cnt_out_sk_spl                   false
% 2.14/1.00  --abstr_cl_out                          false
% 2.14/1.00  
% 2.14/1.00  ------ Global Options
% 2.14/1.00  
% 2.14/1.00  --schedule                              default
% 2.14/1.00  --add_important_lit                     false
% 2.14/1.00  --prop_solver_per_cl                    1000
% 2.14/1.00  --min_unsat_core                        false
% 2.14/1.00  --soft_assumptions                      false
% 2.14/1.00  --soft_lemma_size                       3
% 2.14/1.00  --prop_impl_unit_size                   0
% 2.14/1.00  --prop_impl_unit                        []
% 2.14/1.00  --share_sel_clauses                     true
% 2.14/1.00  --reset_solvers                         false
% 2.14/1.00  --bc_imp_inh                            [conj_cone]
% 2.14/1.00  --conj_cone_tolerance                   3.
% 2.14/1.00  --extra_neg_conj                        none
% 2.14/1.00  --large_theory_mode                     true
% 2.14/1.00  --prolific_symb_bound                   200
% 2.14/1.00  --lt_threshold                          2000
% 2.14/1.00  --clause_weak_htbl                      true
% 2.14/1.00  --gc_record_bc_elim                     false
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing Options
% 2.14/1.00  
% 2.14/1.00  --preprocessing_flag                    true
% 2.14/1.00  --time_out_prep_mult                    0.1
% 2.14/1.00  --splitting_mode                        input
% 2.14/1.00  --splitting_grd                         true
% 2.14/1.00  --splitting_cvd                         false
% 2.14/1.00  --splitting_cvd_svl                     false
% 2.14/1.00  --splitting_nvd                         32
% 2.14/1.00  --sub_typing                            true
% 2.14/1.00  --prep_gs_sim                           true
% 2.14/1.00  --prep_unflatten                        true
% 2.14/1.00  --prep_res_sim                          true
% 2.14/1.00  --prep_upred                            true
% 2.14/1.00  --prep_sem_filter                       exhaustive
% 2.14/1.00  --prep_sem_filter_out                   false
% 2.14/1.00  --pred_elim                             true
% 2.14/1.00  --res_sim_input                         true
% 2.14/1.00  --eq_ax_congr_red                       true
% 2.14/1.00  --pure_diseq_elim                       true
% 2.14/1.00  --brand_transform                       false
% 2.14/1.00  --non_eq_to_eq                          false
% 2.14/1.00  --prep_def_merge                        true
% 2.14/1.00  --prep_def_merge_prop_impl              false
% 2.14/1.00  --prep_def_merge_mbd                    true
% 2.14/1.00  --prep_def_merge_tr_red                 false
% 2.14/1.00  --prep_def_merge_tr_cl                  false
% 2.14/1.00  --smt_preprocessing                     true
% 2.14/1.00  --smt_ac_axioms                         fast
% 2.14/1.00  --preprocessed_out                      false
% 2.14/1.00  --preprocessed_stats                    false
% 2.14/1.00  
% 2.14/1.00  ------ Abstraction refinement Options
% 2.14/1.00  
% 2.14/1.00  --abstr_ref                             []
% 2.14/1.00  --abstr_ref_prep                        false
% 2.14/1.00  --abstr_ref_until_sat                   false
% 2.14/1.00  --abstr_ref_sig_restrict                funpre
% 2.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/1.00  --abstr_ref_under                       []
% 2.14/1.00  
% 2.14/1.00  ------ SAT Options
% 2.14/1.00  
% 2.14/1.00  --sat_mode                              false
% 2.14/1.00  --sat_fm_restart_options                ""
% 2.14/1.00  --sat_gr_def                            false
% 2.14/1.00  --sat_epr_types                         true
% 2.14/1.00  --sat_non_cyclic_types                  false
% 2.14/1.00  --sat_finite_models                     false
% 2.14/1.00  --sat_fm_lemmas                         false
% 2.14/1.00  --sat_fm_prep                           false
% 2.14/1.00  --sat_fm_uc_incr                        true
% 2.14/1.00  --sat_out_model                         small
% 2.14/1.00  --sat_out_clauses                       false
% 2.14/1.00  
% 2.14/1.00  ------ QBF Options
% 2.14/1.00  
% 2.14/1.00  --qbf_mode                              false
% 2.14/1.00  --qbf_elim_univ                         false
% 2.14/1.00  --qbf_dom_inst                          none
% 2.14/1.00  --qbf_dom_pre_inst                      false
% 2.14/1.00  --qbf_sk_in                             false
% 2.14/1.00  --qbf_pred_elim                         true
% 2.14/1.00  --qbf_split                             512
% 2.14/1.00  
% 2.14/1.00  ------ BMC1 Options
% 2.14/1.00  
% 2.14/1.00  --bmc1_incremental                      false
% 2.14/1.00  --bmc1_axioms                           reachable_all
% 2.14/1.00  --bmc1_min_bound                        0
% 2.14/1.00  --bmc1_max_bound                        -1
% 2.14/1.00  --bmc1_max_bound_default                -1
% 2.14/1.00  --bmc1_symbol_reachability              true
% 2.14/1.00  --bmc1_property_lemmas                  false
% 2.14/1.00  --bmc1_k_induction                      false
% 2.14/1.00  --bmc1_non_equiv_states                 false
% 2.14/1.00  --bmc1_deadlock                         false
% 2.14/1.00  --bmc1_ucm                              false
% 2.14/1.00  --bmc1_add_unsat_core                   none
% 2.14/1.00  --bmc1_unsat_core_children              false
% 2.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/1.00  --bmc1_out_stat                         full
% 2.14/1.00  --bmc1_ground_init                      false
% 2.14/1.00  --bmc1_pre_inst_next_state              false
% 2.14/1.00  --bmc1_pre_inst_state                   false
% 2.14/1.00  --bmc1_pre_inst_reach_state             false
% 2.14/1.00  --bmc1_out_unsat_core                   false
% 2.14/1.00  --bmc1_aig_witness_out                  false
% 2.14/1.00  --bmc1_verbose                          false
% 2.14/1.00  --bmc1_dump_clauses_tptp                false
% 2.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.14/1.00  --bmc1_dump_file                        -
% 2.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.14/1.00  --bmc1_ucm_extend_mode                  1
% 2.14/1.00  --bmc1_ucm_init_mode                    2
% 2.14/1.00  --bmc1_ucm_cone_mode                    none
% 2.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.14/1.00  --bmc1_ucm_relax_model                  4
% 2.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/1.00  --bmc1_ucm_layered_model                none
% 2.14/1.00  --bmc1_ucm_max_lemma_size               10
% 2.14/1.00  
% 2.14/1.00  ------ AIG Options
% 2.14/1.00  
% 2.14/1.00  --aig_mode                              false
% 2.14/1.00  
% 2.14/1.00  ------ Instantiation Options
% 2.14/1.00  
% 2.14/1.00  --instantiation_flag                    true
% 2.14/1.00  --inst_sos_flag                         false
% 2.14/1.00  --inst_sos_phase                        true
% 2.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/1.00  --inst_lit_sel_side                     none
% 2.14/1.00  --inst_solver_per_active                1400
% 2.14/1.00  --inst_solver_calls_frac                1.
% 2.14/1.00  --inst_passive_queue_type               priority_queues
% 2.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/1.00  --inst_passive_queues_freq              [25;2]
% 2.14/1.00  --inst_dismatching                      true
% 2.14/1.00  --inst_eager_unprocessed_to_passive     true
% 2.14/1.00  --inst_prop_sim_given                   true
% 2.14/1.00  --inst_prop_sim_new                     false
% 2.14/1.00  --inst_subs_new                         false
% 2.14/1.00  --inst_eq_res_simp                      false
% 2.14/1.00  --inst_subs_given                       false
% 2.14/1.00  --inst_orphan_elimination               true
% 2.14/1.00  --inst_learning_loop_flag               true
% 2.14/1.00  --inst_learning_start                   3000
% 2.14/1.00  --inst_learning_factor                  2
% 2.14/1.00  --inst_start_prop_sim_after_learn       3
% 2.14/1.00  --inst_sel_renew                        solver
% 2.14/1.00  --inst_lit_activity_flag                true
% 2.14/1.00  --inst_restr_to_given                   false
% 2.14/1.00  --inst_activity_threshold               500
% 2.14/1.00  --inst_out_proof                        true
% 2.14/1.00  
% 2.14/1.00  ------ Resolution Options
% 2.14/1.00  
% 2.14/1.00  --resolution_flag                       false
% 2.14/1.00  --res_lit_sel                           adaptive
% 2.14/1.00  --res_lit_sel_side                      none
% 2.14/1.00  --res_ordering                          kbo
% 2.14/1.00  --res_to_prop_solver                    active
% 2.14/1.00  --res_prop_simpl_new                    false
% 2.14/1.00  --res_prop_simpl_given                  true
% 2.14/1.00  --res_passive_queue_type                priority_queues
% 2.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/1.00  --res_passive_queues_freq               [15;5]
% 2.14/1.00  --res_forward_subs                      full
% 2.14/1.00  --res_backward_subs                     full
% 2.14/1.00  --res_forward_subs_resolution           true
% 2.14/1.00  --res_backward_subs_resolution          true
% 2.14/1.00  --res_orphan_elimination                true
% 2.14/1.00  --res_time_limit                        2.
% 2.14/1.00  --res_out_proof                         true
% 2.14/1.00  
% 2.14/1.00  ------ Superposition Options
% 2.14/1.00  
% 2.14/1.00  --superposition_flag                    true
% 2.14/1.00  --sup_passive_queue_type                priority_queues
% 2.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.14/1.00  --demod_completeness_check              fast
% 2.14/1.00  --demod_use_ground                      true
% 2.14/1.00  --sup_to_prop_solver                    passive
% 2.14/1.00  --sup_prop_simpl_new                    true
% 2.14/1.00  --sup_prop_simpl_given                  true
% 2.14/1.00  --sup_fun_splitting                     false
% 2.14/1.00  --sup_smt_interval                      50000
% 2.14/1.00  
% 2.14/1.00  ------ Superposition Simplification Setup
% 2.14/1.00  
% 2.14/1.00  --sup_indices_passive                   []
% 2.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_full_bw                           [BwDemod]
% 2.14/1.00  --sup_immed_triv                        [TrivRules]
% 2.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_immed_bw_main                     []
% 2.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.00  
% 2.14/1.00  ------ Combination Options
% 2.14/1.00  
% 2.14/1.00  --comb_res_mult                         3
% 2.14/1.00  --comb_sup_mult                         2
% 2.14/1.00  --comb_inst_mult                        10
% 2.14/1.00  
% 2.14/1.00  ------ Debug Options
% 2.14/1.00  
% 2.14/1.00  --dbg_backtrace                         false
% 2.14/1.00  --dbg_dump_prop_clauses                 false
% 2.14/1.00  --dbg_dump_prop_clauses_file            -
% 2.14/1.00  --dbg_out_stat                          false
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  ------ Proving...
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  % SZS status Theorem for theBenchmark.p
% 2.14/1.00  
% 2.14/1.00   Resolution empty clause
% 2.14/1.00  
% 2.14/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.14/1.00  
% 2.14/1.00  fof(f4,axiom,(
% 2.14/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.01  
% 2.14/1.01  fof(f35,plain,(
% 2.14/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.14/1.01    inference(nnf_transformation,[],[f4])).
% 2.14/1.01  
% 2.14/1.01  fof(f49,plain,(
% 2.14/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.14/1.01    inference(cnf_transformation,[],[f35])).
% 2.14/1.01  
% 2.14/1.01  fof(f12,axiom,(
% 2.14/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.01  
% 2.14/1.01  fof(f25,plain,(
% 2.14/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/1.01    inference(ennf_transformation,[],[f12])).
% 2.14/1.01  
% 2.14/1.01  fof(f26,plain,(
% 2.14/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/1.01    inference(flattening,[],[f25])).
% 2.14/1.01  
% 2.14/1.01  fof(f38,plain,(
% 2.14/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/1.01    inference(nnf_transformation,[],[f26])).
% 2.14/1.01  
% 2.14/1.01  fof(f66,plain,(
% 2.14/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.14/1.01    inference(cnf_transformation,[],[f38])).
% 2.14/1.01  
% 2.14/1.01  fof(f14,conjecture,(
% 2.14/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.01  
% 2.14/1.01  fof(f15,negated_conjecture,(
% 2.14/1.01    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.14/1.01    inference(negated_conjecture,[],[f14])).
% 2.14/1.01  
% 2.14/1.01  fof(f29,plain,(
% 2.14/1.01    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.14/1.01    inference(ennf_transformation,[],[f15])).
% 2.14/1.01  
% 2.14/1.01  fof(f30,plain,(
% 2.14/1.01    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.14/1.01    inference(flattening,[],[f29])).
% 2.14/1.01  
% 2.14/1.01  fof(f39,plain,(
% 2.14/1.01    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.14/1.01    introduced(choice_axiom,[])).
% 2.14/1.01  
% 2.14/1.01  fof(f40,plain,(
% 2.14/1.01    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.14/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f39])).
% 2.14/1.01  
% 2.14/1.01  fof(f76,plain,(
% 2.14/1.01    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)),
% 2.14/1.01    inference(cnf_transformation,[],[f40])).
% 2.14/1.01  
% 2.14/1.01  fof(f74,plain,(
% 2.14/1.01    v1_funct_1(sK2)),
% 2.14/1.01    inference(cnf_transformation,[],[f40])).
% 2.14/1.01  
% 2.14/1.01  fof(f10,axiom,(
% 2.14/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.01  
% 2.14/1.01  fof(f22,plain,(
% 2.14/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/1.01    inference(ennf_transformation,[],[f10])).
% 2.14/1.01  
% 2.14/1.01  fof(f62,plain,(
% 2.14/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.14/1.01    inference(cnf_transformation,[],[f22])).
% 2.14/1.01  
% 2.14/1.01  fof(f73,plain,(
% 2.14/1.01    v1_relat_1(sK2)),
% 2.14/1.01    inference(cnf_transformation,[],[f40])).
% 2.14/1.01  
% 2.14/1.01  fof(f75,plain,(
% 2.14/1.01    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.14/1.01    inference(cnf_transformation,[],[f40])).
% 2.14/1.01  
% 2.14/1.01  fof(f1,axiom,(
% 2.14/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.01  
% 2.14/1.01  fof(f31,plain,(
% 2.14/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/1.01    inference(nnf_transformation,[],[f1])).
% 2.14/1.01  
% 2.14/1.01  fof(f32,plain,(
% 2.14/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/1.01    inference(flattening,[],[f31])).
% 2.14/1.01  
% 2.14/1.01  fof(f42,plain,(
% 2.14/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.14/1.01    inference(cnf_transformation,[],[f32])).
% 2.14/1.01  
% 2.14/1.01  fof(f77,plain,(
% 2.14/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.14/1.01    inference(equality_resolution,[],[f42])).
% 2.14/1.01  
% 2.14/1.01  fof(f11,axiom,(
% 2.14/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.01  
% 2.14/1.01  fof(f23,plain,(
% 2.14/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.14/1.01    inference(ennf_transformation,[],[f11])).
% 2.14/1.01  
% 2.14/1.01  fof(f24,plain,(
% 2.14/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.14/1.01    inference(flattening,[],[f23])).
% 2.14/1.01  
% 2.14/1.01  fof(f63,plain,(
% 2.14/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.14/1.01    inference(cnf_transformation,[],[f24])).
% 2.14/1.01  
% 2.14/1.01  fof(f43,plain,(
% 2.14/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.14/1.01    inference(cnf_transformation,[],[f32])).
% 2.14/1.01  
% 2.14/1.01  fof(f13,axiom,(
% 2.14/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.01  
% 2.14/1.01  fof(f27,plain,(
% 2.14/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/1.01    inference(ennf_transformation,[],[f13])).
% 2.14/1.01  
% 2.14/1.01  fof(f28,plain,(
% 2.14/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/1.01    inference(flattening,[],[f27])).
% 2.14/1.01  
% 2.14/1.01  fof(f71,plain,(
% 2.14/1.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/1.01    inference(cnf_transformation,[],[f28])).
% 2.14/1.01  
% 2.14/1.01  fof(f3,axiom,(
% 2.14/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.14/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.01  
% 2.14/1.01  fof(f47,plain,(
% 2.14/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.14/1.01    inference(cnf_transformation,[],[f3])).
% 2.14/1.01  
% 2.14/1.01  fof(f48,plain,(
% 2.14/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.14/1.01    inference(cnf_transformation,[],[f35])).
% 2.14/1.01  
% 2.14/1.01  cnf(c_7,plain,
% 2.14/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.14/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2268,plain,
% 2.14/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.14/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.14/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_26,plain,
% 2.14/1.01      ( v1_funct_2(X0,X1,X2)
% 2.14/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.14/1.01      | k1_relset_1(X1,X2,X0) != X1
% 2.14/1.01      | k1_xboole_0 = X2 ),
% 2.14/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_32,negated_conjecture,
% 2.14/1.01      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 2.14/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | ~ v1_funct_1(sK2) ),
% 2.14/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_34,negated_conjecture,
% 2.14/1.01      ( v1_funct_1(sK2) ),
% 2.14/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_175,plain,
% 2.14/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
% 2.14/1.01      inference(global_propositional_subsumption,[status(thm)],[c_32,c_34]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_176,negated_conjecture,
% 2.14/1.01      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 2.14/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
% 2.14/1.01      inference(renaming,[status(thm)],[c_175]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_798,plain,
% 2.14/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.14/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | k1_relset_1(X1,X2,X0) != X1
% 2.14/1.01      | k1_relat_1(sK2) != X1
% 2.14/1.01      | sK1 != X2
% 2.14/1.01      | sK2 != X0
% 2.14/1.01      | k1_xboole_0 = X2 ),
% 2.14/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_176]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_799,plain,
% 2.14/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
% 2.14/1.01      | k1_xboole_0 = sK1 ),
% 2.14/1.01      inference(unflattening,[status(thm)],[c_798]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_21,plain,
% 2.14/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.14/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.14/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_807,plain,
% 2.14/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | k1_xboole_0 = sK1 ),
% 2.14/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_799,c_21]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2247,plain,
% 2.14/1.01      ( k1_xboole_0 = sK1
% 2.14/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
% 2.14/1.01      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_3107,plain,
% 2.14/1.01      ( sK1 = k1_xboole_0
% 2.14/1.01      | r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK1)) != iProver_top ),
% 2.14/1.01      inference(superposition,[status(thm)],[c_2268,c_2247]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_35,negated_conjecture,
% 2.14/1.01      ( v1_relat_1(sK2) ),
% 2.14/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_33,negated_conjecture,
% 2.14/1.01      ( r1_tarski(k2_relat_1(sK2),sK1) ),
% 2.14/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f77]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2635,plain,
% 2.14/1.01      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_22,plain,
% 2.14/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.14/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.14/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.14/1.01      | ~ v1_relat_1(X0) ),
% 2.14/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2571,plain,
% 2.14/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.14/1.01      | ~ r1_tarski(k1_relat_1(sK2),X0)
% 2.14/1.01      | ~ r1_tarski(k2_relat_1(sK2),X1)
% 2.14/1.01      | ~ v1_relat_1(sK2) ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2634,plain,
% 2.14/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 2.14/1.01      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
% 2.14/1.01      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 2.14/1.01      | ~ v1_relat_1(sK2) ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_2571]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2747,plain,
% 2.14/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
% 2.14/1.01      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 2.14/1.01      | ~ v1_relat_1(sK2) ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_2634]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_1626,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2588,plain,
% 2.14/1.01      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_1626]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2841,plain,
% 2.14/1.01      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_2588]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_1625,plain,( X0 = X0 ),theory(equality) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2842,plain,
% 2.14/1.01      ( sK1 = sK1 ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_1625]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_3196,plain,
% 2.14/1.01      ( sK1 = k1_xboole_0 ),
% 2.14/1.01      inference(global_propositional_subsumption,
% 2.14/1.01                [status(thm)],
% 2.14/1.01                [c_3107,c_35,c_33,c_807,c_2635,c_2747,c_2841,c_2842]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2256,plain,
% 2.14/1.01      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 2.14/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_3203,plain,
% 2.14/1.01      ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 2.14/1.01      inference(demodulation,[status(thm)],[c_3196,c_2256]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_0,plain,
% 2.14/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.14/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2271,plain,
% 2.14/1.01      ( X0 = X1
% 2.14/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.14/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.14/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_4082,plain,
% 2.14/1.01      ( k2_relat_1(sK2) = k1_xboole_0
% 2.14/1.01      | r1_tarski(k1_xboole_0,k2_relat_1(sK2)) != iProver_top ),
% 2.14/1.01      inference(superposition,[status(thm)],[c_3203,c_2271]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_30,plain,
% 2.14/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.14/1.01      | ~ v1_relat_1(X0)
% 2.14/1.01      | ~ v1_funct_1(X0) ),
% 2.14/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_811,plain,
% 2.14/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | ~ v1_relat_1(X0)
% 2.14/1.01      | ~ v1_funct_1(X0)
% 2.14/1.01      | k1_relat_1(X0) != k1_relat_1(sK2)
% 2.14/1.01      | k2_relat_1(X0) != sK1
% 2.14/1.01      | sK2 != X0 ),
% 2.14/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_176]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_812,plain,
% 2.14/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | ~ v1_relat_1(sK2)
% 2.14/1.01      | ~ v1_funct_1(sK2)
% 2.14/1.01      | k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.14/1.01      | k2_relat_1(sK2) != sK1 ),
% 2.14/1.01      inference(unflattening,[status(thm)],[c_811]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_814,plain,
% 2.14/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.14/1.01      | k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.14/1.01      | k2_relat_1(sK2) != sK1 ),
% 2.14/1.01      inference(global_propositional_subsumption,
% 2.14/1.01                [status(thm)],
% 2.14/1.01                [c_812,c_35,c_34]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2590,plain,
% 2.14/1.01      ( k2_relat_1(sK2) != X0 | k2_relat_1(sK2) = sK1 | sK1 != X0 ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_1626]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2591,plain,
% 2.14/1.01      ( k2_relat_1(sK2) = sK1
% 2.14/1.01      | k2_relat_1(sK2) != k1_xboole_0
% 2.14/1.01      | sK1 != k1_xboole_0 ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_2590]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2655,plain,
% 2.14/1.01      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_1625]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_3245,plain,
% 2.14/1.01      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 2.14/1.01      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 2.14/1.01      | k2_relat_1(sK2) = X0 ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_3246,plain,
% 2.14/1.01      ( k2_relat_1(sK2) = X0
% 2.14/1.01      | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
% 2.14/1.01      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 2.14/1.01      inference(predicate_to_equality,[status(thm)],[c_3245]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_3248,plain,
% 2.14/1.01      ( k2_relat_1(sK2) = k1_xboole_0
% 2.14/1.01      | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
% 2.14/1.01      | r1_tarski(k1_xboole_0,k2_relat_1(sK2)) != iProver_top ),
% 2.14/1.01      inference(instantiation,[status(thm)],[c_3246]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_4345,plain,
% 2.14/1.01      ( r1_tarski(k1_xboole_0,k2_relat_1(sK2)) != iProver_top ),
% 2.14/1.01      inference(global_propositional_subsumption,
% 2.14/1.01                [status(thm)],
% 2.14/1.01                [c_4082,c_35,c_33,c_807,c_814,c_2591,c_2635,c_2655,c_2747,
% 2.14/1.01                 c_2841,c_2842,c_3203,c_3248]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_6,plain,
% 2.14/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.14/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2269,plain,
% 2.14/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.14/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_8,plain,
% 2.14/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.14/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_2267,plain,
% 2.14/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.14/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.14/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_3075,plain,
% 2.14/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.14/1.01      inference(superposition,[status(thm)],[c_2269,c_2267]) ).
% 2.14/1.01  
% 2.14/1.01  cnf(c_4350,plain,
% 2.14/1.01      ( $false ),
% 2.14/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4345,c_3075]) ).
% 2.14/1.01  
% 2.14/1.01  
% 2.14/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.14/1.01  
% 2.14/1.01  ------                               Statistics
% 2.14/1.01  
% 2.14/1.01  ------ General
% 2.14/1.01  
% 2.14/1.01  abstr_ref_over_cycles:                  0
% 2.14/1.01  abstr_ref_under_cycles:                 0
% 2.14/1.01  gc_basic_clause_elim:                   0
% 2.14/1.01  forced_gc_time:                         0
% 2.14/1.01  parsing_time:                           0.011
% 2.14/1.01  unif_index_cands_time:                  0.
% 2.14/1.01  unif_index_add_time:                    0.
% 2.14/1.01  orderings_time:                         0.
% 2.14/1.01  out_proof_time:                         0.01
% 2.14/1.01  total_time:                             0.172
% 2.14/1.01  num_of_symbols:                         45
% 2.14/1.01  num_of_terms:                           3004
% 2.14/1.01  
% 2.14/1.01  ------ Preprocessing
% 2.14/1.01  
% 2.14/1.01  num_of_splits:                          0
% 2.14/1.01  num_of_split_atoms:                     0
% 2.14/1.01  num_of_reused_defs:                     0
% 2.14/1.01  num_eq_ax_congr_red:                    5
% 2.14/1.01  num_of_sem_filtered_clauses:            1
% 2.14/1.01  num_of_subtypes:                        0
% 2.14/1.01  monotx_restored_types:                  0
% 2.14/1.01  sat_num_of_epr_types:                   0
% 2.14/1.01  sat_num_of_non_cyclic_types:            0
% 2.14/1.01  sat_guarded_non_collapsed_types:        0
% 2.14/1.01  num_pure_diseq_elim:                    0
% 2.14/1.01  simp_replaced_by:                       0
% 2.14/1.01  res_preprocessed:                       158
% 2.14/1.01  prep_upred:                             0
% 2.14/1.01  prep_unflattend:                        73
% 2.14/1.01  smt_new_axioms:                         0
% 2.14/1.01  pred_elim_cands:                        4
% 2.14/1.01  pred_elim:                              1
% 2.14/1.01  pred_elim_cl:                           1
% 2.14/1.01  pred_elim_cycles:                       4
% 2.14/1.01  merged_defs:                            8
% 2.14/1.01  merged_defs_ncl:                        0
% 2.14/1.01  bin_hyper_res:                          9
% 2.14/1.01  prep_cycles:                            4
% 2.14/1.01  pred_elim_time:                         0.026
% 2.14/1.01  splitting_time:                         0.
% 2.14/1.01  sem_filter_time:                        0.
% 2.14/1.01  monotx_time:                            0.001
% 2.14/1.01  subtype_inf_time:                       0.
% 2.14/1.01  
% 2.14/1.01  ------ Problem properties
% 2.14/1.01  
% 2.14/1.01  clauses:                                33
% 2.14/1.01  conjectures:                            3
% 2.14/1.01  epr:                                    5
% 2.14/1.01  horn:                                   26
% 2.14/1.01  ground:                                 9
% 2.14/1.01  unary:                                  13
% 2.14/1.01  binary:                                 10
% 2.14/1.01  lits:                                   71
% 2.14/1.01  lits_eq:                                29
% 2.14/1.01  fd_pure:                                0
% 2.14/1.01  fd_pseudo:                              0
% 2.14/1.01  fd_cond:                                5
% 2.14/1.01  fd_pseudo_cond:                         1
% 2.14/1.01  ac_symbols:                             0
% 2.14/1.01  
% 2.14/1.01  ------ Propositional Solver
% 2.14/1.01  
% 2.14/1.01  prop_solver_calls:                      27
% 2.14/1.01  prop_fast_solver_calls:                 1051
% 2.14/1.01  smt_solver_calls:                       0
% 2.14/1.01  smt_fast_solver_calls:                  0
% 2.14/1.01  prop_num_of_clauses:                    1189
% 2.14/1.01  prop_preprocess_simplified:             5411
% 2.14/1.01  prop_fo_subsumed:                       37
% 2.14/1.01  prop_solver_time:                       0.
% 2.14/1.01  smt_solver_time:                        0.
% 2.14/1.01  smt_fast_solver_time:                   0.
% 2.14/1.01  prop_fast_solver_time:                  0.
% 2.14/1.01  prop_unsat_core_time:                   0.
% 2.14/1.01  
% 2.14/1.01  ------ QBF
% 2.14/1.01  
% 2.14/1.01  qbf_q_res:                              0
% 2.14/1.01  qbf_num_tautologies:                    0
% 2.14/1.01  qbf_prep_cycles:                        0
% 2.14/1.01  
% 2.14/1.01  ------ BMC1
% 2.14/1.01  
% 2.14/1.01  bmc1_current_bound:                     -1
% 2.14/1.01  bmc1_last_solved_bound:                 -1
% 2.14/1.01  bmc1_unsat_core_size:                   -1
% 2.14/1.01  bmc1_unsat_core_parents_size:           -1
% 2.14/1.01  bmc1_merge_next_fun:                    0
% 2.14/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.14/1.01  
% 2.14/1.01  ------ Instantiation
% 2.14/1.01  
% 2.14/1.01  inst_num_of_clauses:                    334
% 2.14/1.01  inst_num_in_passive:                    114
% 2.14/1.01  inst_num_in_active:                     197
% 2.14/1.01  inst_num_in_unprocessed:                23
% 2.14/1.01  inst_num_of_loops:                      260
% 2.14/1.01  inst_num_of_learning_restarts:          0
% 2.14/1.01  inst_num_moves_active_passive:          60
% 2.14/1.01  inst_lit_activity:                      0
% 2.14/1.01  inst_lit_activity_moves:                0
% 2.14/1.01  inst_num_tautologies:                   0
% 2.14/1.01  inst_num_prop_implied:                  0
% 2.14/1.01  inst_num_existing_simplified:           0
% 2.14/1.01  inst_num_eq_res_simplified:             0
% 2.14/1.01  inst_num_child_elim:                    0
% 2.14/1.01  inst_num_of_dismatching_blockings:      74
% 2.14/1.01  inst_num_of_non_proper_insts:           278
% 2.14/1.01  inst_num_of_duplicates:                 0
% 2.14/1.01  inst_inst_num_from_inst_to_res:         0
% 2.14/1.01  inst_dismatching_checking_time:         0.
% 2.14/1.01  
% 2.14/1.01  ------ Resolution
% 2.14/1.01  
% 2.14/1.01  res_num_of_clauses:                     0
% 2.14/1.01  res_num_in_passive:                     0
% 2.14/1.01  res_num_in_active:                      0
% 2.14/1.01  res_num_of_loops:                       162
% 2.14/1.01  res_forward_subset_subsumed:            16
% 2.14/1.01  res_backward_subset_subsumed:           0
% 2.14/1.01  res_forward_subsumed:                   0
% 2.14/1.01  res_backward_subsumed:                  0
% 2.14/1.01  res_forward_subsumption_resolution:     6
% 2.14/1.01  res_backward_subsumption_resolution:    0
% 2.14/1.01  res_clause_to_clause_subsumption:       323
% 2.14/1.01  res_orphan_elimination:                 0
% 2.14/1.01  res_tautology_del:                      34
% 2.14/1.01  res_num_eq_res_simplified:              1
% 2.14/1.01  res_num_sel_changes:                    0
% 2.14/1.01  res_moves_from_active_to_pass:          0
% 2.14/1.01  
% 2.14/1.01  ------ Superposition
% 2.14/1.01  
% 2.14/1.01  sup_time_total:                         0.
% 2.14/1.01  sup_time_generating:                    0.
% 2.14/1.01  sup_time_sim_full:                      0.
% 2.14/1.01  sup_time_sim_immed:                     0.
% 2.14/1.01  
% 2.14/1.01  sup_num_of_clauses:                     71
% 2.14/1.01  sup_num_in_active:                      46
% 2.14/1.01  sup_num_in_passive:                     25
% 2.14/1.01  sup_num_of_loops:                       51
% 2.14/1.01  sup_fw_superposition:                   50
% 2.14/1.01  sup_bw_superposition:                   13
% 2.14/1.01  sup_immediate_simplified:               13
% 2.14/1.01  sup_given_eliminated:                   0
% 2.14/1.01  comparisons_done:                       0
% 2.14/1.01  comparisons_avoided:                    6
% 2.14/1.01  
% 2.14/1.01  ------ Simplifications
% 2.14/1.01  
% 2.14/1.01  
% 2.14/1.01  sim_fw_subset_subsumed:                 1
% 2.14/1.01  sim_bw_subset_subsumed:                 0
% 2.14/1.01  sim_fw_subsumed:                        4
% 2.14/1.01  sim_bw_subsumed:                        0
% 2.14/1.01  sim_fw_subsumption_res:                 1
% 2.14/1.01  sim_bw_subsumption_res:                 0
% 2.14/1.01  sim_tautology_del:                      3
% 2.14/1.01  sim_eq_tautology_del:                   4
% 2.14/1.01  sim_eq_res_simp:                        1
% 2.14/1.01  sim_fw_demodulated:                     11
% 2.14/1.01  sim_bw_demodulated:                     5
% 2.14/1.01  sim_light_normalised:                   6
% 2.14/1.01  sim_joinable_taut:                      0
% 2.14/1.01  sim_joinable_simp:                      0
% 2.14/1.01  sim_ac_normalised:                      0
% 2.14/1.01  sim_smt_subsumption:                    0
% 2.14/1.01  
%------------------------------------------------------------------------------
