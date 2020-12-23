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
% DateTime   : Thu Dec  3 11:59:56 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 892 expanded)
%              Number of clauses        :   77 ( 318 expanded)
%              Number of leaves         :   10 ( 147 expanded)
%              Depth                    :   24
%              Number of atoms          :  399 (3424 expanded)
%              Number of equality atoms :  197 (1067 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f30])).

fof(f57,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_124,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_24])).

cnf(c_125,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK0) != X1
    | k2_relat_1(sK0) != X2
    | sK0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_125])).

cnf(c_356,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_364,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_356,c_15])).

cnf(c_905,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_1812,plain,
    ( k2_relat_1(sK0) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_905])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1587,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1590,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1587])).

cnf(c_2180,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
    | k2_relat_1(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1812,c_26,c_1590])).

cnf(c_2181,plain,
    ( k2_relat_1(sK0) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2180])).

cnf(c_917,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2186,plain,
    ( k2_relat_1(sK0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2181,c_917])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1808,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_910])).

cnf(c_2997,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_1808])).

cnf(c_3615,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2186,c_2997])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_70,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_72,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_4019,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3615,c_26,c_72])).

cnf(c_17,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_312,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_relat_1(sK0) != X0
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_125])).

cnf(c_313,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_907,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_996,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_907,c_5])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_65,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_67,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_1067,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | sK0 != k1_xboole_0
    | k2_relat_1(sK0) != k1_xboole_0
    | k1_relat_1(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_67,c_72])).

cnf(c_1068,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1067])).

cnf(c_2187,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2186,c_1068])).

cnf(c_2198,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2187])).

cnf(c_2202,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2198,c_5])).

cnf(c_66,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_71,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1008,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(sK0) = k1_xboole_0
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_996])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1082,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1083,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1082])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1097,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1098,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_1463,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1663,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1666,plain,
    ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1663])).

cnf(c_1056,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1326,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X0))))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_2124,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2347,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2371,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_25,c_66,c_71,c_1008,c_1083,c_1098,c_1463,c_1587,c_1666,c_2124,c_2186,c_2347])).

cnf(c_4025,plain,
    ( k1_relat_1(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4019,c_2371])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_911,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1490,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_911])).

cnf(c_4026,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK0) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_4019,c_1490])).

cnf(c_4033,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4025,c_4026])).

cnf(c_4040,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4033])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | k2_relat_1(sK0) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_125])).

cnf(c_340,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_906,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_987,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_906,c_6])).

cnf(c_2188,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2186,c_987])).

cnf(c_2194,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2188,c_5])).

cnf(c_2364,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_25,c_66,c_71,c_1008,c_1083,c_1098,c_1463,c_1587,c_1666,c_2124,c_2186,c_2347])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4040,c_3615,c_2364,c_72,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.10/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.01  
% 2.10/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.10/1.01  
% 2.10/1.01  ------  iProver source info
% 2.10/1.01  
% 2.10/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.10/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.10/1.01  git: non_committed_changes: false
% 2.10/1.01  git: last_make_outside_of_git: false
% 2.10/1.01  
% 2.10/1.01  ------ 
% 2.10/1.01  
% 2.10/1.01  ------ Input Options
% 2.10/1.01  
% 2.10/1.01  --out_options                           all
% 2.10/1.01  --tptp_safe_out                         true
% 2.10/1.01  --problem_path                          ""
% 2.10/1.01  --include_path                          ""
% 2.10/1.01  --clausifier                            res/vclausify_rel
% 2.10/1.01  --clausifier_options                    --mode clausify
% 2.10/1.01  --stdin                                 false
% 2.10/1.01  --stats_out                             all
% 2.10/1.01  
% 2.10/1.01  ------ General Options
% 2.10/1.01  
% 2.10/1.01  --fof                                   false
% 2.10/1.01  --time_out_real                         305.
% 2.10/1.01  --time_out_virtual                      -1.
% 2.10/1.01  --symbol_type_check                     false
% 2.10/1.01  --clausify_out                          false
% 2.10/1.01  --sig_cnt_out                           false
% 2.10/1.01  --trig_cnt_out                          false
% 2.10/1.01  --trig_cnt_out_tolerance                1.
% 2.10/1.01  --trig_cnt_out_sk_spl                   false
% 2.10/1.01  --abstr_cl_out                          false
% 2.10/1.01  
% 2.10/1.01  ------ Global Options
% 2.10/1.01  
% 2.10/1.01  --schedule                              default
% 2.10/1.01  --add_important_lit                     false
% 2.10/1.01  --prop_solver_per_cl                    1000
% 2.10/1.01  --min_unsat_core                        false
% 2.10/1.01  --soft_assumptions                      false
% 2.10/1.01  --soft_lemma_size                       3
% 2.10/1.01  --prop_impl_unit_size                   0
% 2.10/1.01  --prop_impl_unit                        []
% 2.10/1.01  --share_sel_clauses                     true
% 2.10/1.01  --reset_solvers                         false
% 2.10/1.01  --bc_imp_inh                            [conj_cone]
% 2.10/1.01  --conj_cone_tolerance                   3.
% 2.10/1.01  --extra_neg_conj                        none
% 2.10/1.01  --large_theory_mode                     true
% 2.10/1.01  --prolific_symb_bound                   200
% 2.10/1.01  --lt_threshold                          2000
% 2.10/1.01  --clause_weak_htbl                      true
% 2.10/1.01  --gc_record_bc_elim                     false
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing Options
% 2.10/1.01  
% 2.10/1.01  --preprocessing_flag                    true
% 2.10/1.01  --time_out_prep_mult                    0.1
% 2.10/1.01  --splitting_mode                        input
% 2.10/1.01  --splitting_grd                         true
% 2.10/1.01  --splitting_cvd                         false
% 2.10/1.01  --splitting_cvd_svl                     false
% 2.10/1.01  --splitting_nvd                         32
% 2.10/1.01  --sub_typing                            true
% 2.10/1.01  --prep_gs_sim                           true
% 2.10/1.01  --prep_unflatten                        true
% 2.10/1.01  --prep_res_sim                          true
% 2.10/1.01  --prep_upred                            true
% 2.10/1.01  --prep_sem_filter                       exhaustive
% 2.10/1.01  --prep_sem_filter_out                   false
% 2.10/1.01  --pred_elim                             true
% 2.10/1.01  --res_sim_input                         true
% 2.10/1.01  --eq_ax_congr_red                       true
% 2.10/1.01  --pure_diseq_elim                       true
% 2.10/1.01  --brand_transform                       false
% 2.10/1.01  --non_eq_to_eq                          false
% 2.10/1.01  --prep_def_merge                        true
% 2.10/1.01  --prep_def_merge_prop_impl              false
% 2.10/1.01  --prep_def_merge_mbd                    true
% 2.10/1.01  --prep_def_merge_tr_red                 false
% 2.10/1.01  --prep_def_merge_tr_cl                  false
% 2.10/1.01  --smt_preprocessing                     true
% 2.10/1.01  --smt_ac_axioms                         fast
% 2.10/1.01  --preprocessed_out                      false
% 2.10/1.01  --preprocessed_stats                    false
% 2.10/1.01  
% 2.10/1.01  ------ Abstraction refinement Options
% 2.10/1.01  
% 2.10/1.01  --abstr_ref                             []
% 2.10/1.01  --abstr_ref_prep                        false
% 2.10/1.01  --abstr_ref_until_sat                   false
% 2.10/1.01  --abstr_ref_sig_restrict                funpre
% 2.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.01  --abstr_ref_under                       []
% 2.10/1.01  
% 2.10/1.01  ------ SAT Options
% 2.10/1.01  
% 2.10/1.01  --sat_mode                              false
% 2.10/1.01  --sat_fm_restart_options                ""
% 2.10/1.01  --sat_gr_def                            false
% 2.10/1.01  --sat_epr_types                         true
% 2.10/1.01  --sat_non_cyclic_types                  false
% 2.10/1.01  --sat_finite_models                     false
% 2.10/1.01  --sat_fm_lemmas                         false
% 2.10/1.01  --sat_fm_prep                           false
% 2.10/1.01  --sat_fm_uc_incr                        true
% 2.10/1.01  --sat_out_model                         small
% 2.10/1.01  --sat_out_clauses                       false
% 2.10/1.01  
% 2.10/1.01  ------ QBF Options
% 2.10/1.01  
% 2.10/1.01  --qbf_mode                              false
% 2.10/1.01  --qbf_elim_univ                         false
% 2.10/1.01  --qbf_dom_inst                          none
% 2.10/1.01  --qbf_dom_pre_inst                      false
% 2.10/1.01  --qbf_sk_in                             false
% 2.10/1.01  --qbf_pred_elim                         true
% 2.10/1.01  --qbf_split                             512
% 2.10/1.01  
% 2.10/1.01  ------ BMC1 Options
% 2.10/1.01  
% 2.10/1.01  --bmc1_incremental                      false
% 2.10/1.01  --bmc1_axioms                           reachable_all
% 2.10/1.01  --bmc1_min_bound                        0
% 2.10/1.01  --bmc1_max_bound                        -1
% 2.10/1.01  --bmc1_max_bound_default                -1
% 2.10/1.01  --bmc1_symbol_reachability              true
% 2.10/1.01  --bmc1_property_lemmas                  false
% 2.10/1.01  --bmc1_k_induction                      false
% 2.10/1.01  --bmc1_non_equiv_states                 false
% 2.10/1.01  --bmc1_deadlock                         false
% 2.10/1.01  --bmc1_ucm                              false
% 2.10/1.01  --bmc1_add_unsat_core                   none
% 2.10/1.01  --bmc1_unsat_core_children              false
% 2.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.01  --bmc1_out_stat                         full
% 2.10/1.01  --bmc1_ground_init                      false
% 2.10/1.01  --bmc1_pre_inst_next_state              false
% 2.10/1.01  --bmc1_pre_inst_state                   false
% 2.10/1.01  --bmc1_pre_inst_reach_state             false
% 2.10/1.01  --bmc1_out_unsat_core                   false
% 2.10/1.01  --bmc1_aig_witness_out                  false
% 2.10/1.01  --bmc1_verbose                          false
% 2.10/1.01  --bmc1_dump_clauses_tptp                false
% 2.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.01  --bmc1_dump_file                        -
% 2.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.01  --bmc1_ucm_extend_mode                  1
% 2.10/1.01  --bmc1_ucm_init_mode                    2
% 2.10/1.01  --bmc1_ucm_cone_mode                    none
% 2.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.01  --bmc1_ucm_relax_model                  4
% 2.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.01  --bmc1_ucm_layered_model                none
% 2.10/1.01  --bmc1_ucm_max_lemma_size               10
% 2.10/1.01  
% 2.10/1.01  ------ AIG Options
% 2.10/1.01  
% 2.10/1.01  --aig_mode                              false
% 2.10/1.01  
% 2.10/1.01  ------ Instantiation Options
% 2.10/1.01  
% 2.10/1.01  --instantiation_flag                    true
% 2.10/1.01  --inst_sos_flag                         false
% 2.10/1.01  --inst_sos_phase                        true
% 2.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.01  --inst_lit_sel_side                     num_symb
% 2.10/1.01  --inst_solver_per_active                1400
% 2.10/1.01  --inst_solver_calls_frac                1.
% 2.10/1.01  --inst_passive_queue_type               priority_queues
% 2.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.01  --inst_passive_queues_freq              [25;2]
% 2.10/1.01  --inst_dismatching                      true
% 2.10/1.01  --inst_eager_unprocessed_to_passive     true
% 2.10/1.01  --inst_prop_sim_given                   true
% 2.10/1.01  --inst_prop_sim_new                     false
% 2.10/1.01  --inst_subs_new                         false
% 2.10/1.01  --inst_eq_res_simp                      false
% 2.10/1.01  --inst_subs_given                       false
% 2.10/1.01  --inst_orphan_elimination               true
% 2.10/1.01  --inst_learning_loop_flag               true
% 2.10/1.01  --inst_learning_start                   3000
% 2.10/1.01  --inst_learning_factor                  2
% 2.10/1.01  --inst_start_prop_sim_after_learn       3
% 2.10/1.01  --inst_sel_renew                        solver
% 2.10/1.01  --inst_lit_activity_flag                true
% 2.10/1.01  --inst_restr_to_given                   false
% 2.10/1.01  --inst_activity_threshold               500
% 2.10/1.01  --inst_out_proof                        true
% 2.10/1.01  
% 2.10/1.01  ------ Resolution Options
% 2.10/1.01  
% 2.10/1.01  --resolution_flag                       true
% 2.10/1.01  --res_lit_sel                           adaptive
% 2.10/1.01  --res_lit_sel_side                      none
% 2.10/1.01  --res_ordering                          kbo
% 2.10/1.01  --res_to_prop_solver                    active
% 2.10/1.01  --res_prop_simpl_new                    false
% 2.10/1.01  --res_prop_simpl_given                  true
% 2.10/1.01  --res_passive_queue_type                priority_queues
% 2.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.01  --res_passive_queues_freq               [15;5]
% 2.10/1.01  --res_forward_subs                      full
% 2.10/1.01  --res_backward_subs                     full
% 2.10/1.01  --res_forward_subs_resolution           true
% 2.10/1.01  --res_backward_subs_resolution          true
% 2.10/1.01  --res_orphan_elimination                true
% 2.10/1.01  --res_time_limit                        2.
% 2.10/1.01  --res_out_proof                         true
% 2.10/1.01  
% 2.10/1.01  ------ Superposition Options
% 2.10/1.01  
% 2.10/1.01  --superposition_flag                    true
% 2.10/1.01  --sup_passive_queue_type                priority_queues
% 2.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.01  --demod_completeness_check              fast
% 2.10/1.01  --demod_use_ground                      true
% 2.10/1.01  --sup_to_prop_solver                    passive
% 2.10/1.01  --sup_prop_simpl_new                    true
% 2.10/1.01  --sup_prop_simpl_given                  true
% 2.10/1.01  --sup_fun_splitting                     false
% 2.10/1.01  --sup_smt_interval                      50000
% 2.10/1.01  
% 2.10/1.01  ------ Superposition Simplification Setup
% 2.10/1.01  
% 2.10/1.01  --sup_indices_passive                   []
% 2.10/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_full_bw                           [BwDemod]
% 2.10/1.01  --sup_immed_triv                        [TrivRules]
% 2.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_immed_bw_main                     []
% 2.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.01  
% 2.10/1.01  ------ Combination Options
% 2.10/1.01  
% 2.10/1.01  --comb_res_mult                         3
% 2.10/1.01  --comb_sup_mult                         2
% 2.10/1.01  --comb_inst_mult                        10
% 2.10/1.01  
% 2.10/1.01  ------ Debug Options
% 2.10/1.01  
% 2.10/1.01  --dbg_backtrace                         false
% 2.10/1.01  --dbg_dump_prop_clauses                 false
% 2.10/1.01  --dbg_dump_prop_clauses_file            -
% 2.10/1.01  --dbg_out_stat                          false
% 2.10/1.01  ------ Parsing...
% 2.10/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.10/1.01  ------ Proving...
% 2.10/1.01  ------ Problem Properties 
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  clauses                                 19
% 2.10/1.01  conjectures                             1
% 2.10/1.01  EPR                                     5
% 2.10/1.01  Horn                                    18
% 2.10/1.01  unary                                   8
% 2.10/1.01  binary                                  4
% 2.10/1.01  lits                                    43
% 2.10/1.01  lits eq                                 15
% 2.10/1.01  fd_pure                                 0
% 2.10/1.01  fd_pseudo                               0
% 2.10/1.01  fd_cond                                 1
% 2.10/1.01  fd_pseudo_cond                          1
% 2.10/1.01  AC symbols                              0
% 2.10/1.01  
% 2.10/1.01  ------ Schedule dynamic 5 is on 
% 2.10/1.01  
% 2.10/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  ------ 
% 2.10/1.01  Current options:
% 2.10/1.01  ------ 
% 2.10/1.01  
% 2.10/1.01  ------ Input Options
% 2.10/1.01  
% 2.10/1.01  --out_options                           all
% 2.10/1.01  --tptp_safe_out                         true
% 2.10/1.01  --problem_path                          ""
% 2.10/1.01  --include_path                          ""
% 2.10/1.01  --clausifier                            res/vclausify_rel
% 2.10/1.01  --clausifier_options                    --mode clausify
% 2.10/1.01  --stdin                                 false
% 2.10/1.01  --stats_out                             all
% 2.10/1.01  
% 2.10/1.01  ------ General Options
% 2.10/1.01  
% 2.10/1.01  --fof                                   false
% 2.10/1.01  --time_out_real                         305.
% 2.10/1.01  --time_out_virtual                      -1.
% 2.10/1.01  --symbol_type_check                     false
% 2.10/1.01  --clausify_out                          false
% 2.10/1.01  --sig_cnt_out                           false
% 2.10/1.01  --trig_cnt_out                          false
% 2.10/1.01  --trig_cnt_out_tolerance                1.
% 2.10/1.01  --trig_cnt_out_sk_spl                   false
% 2.10/1.01  --abstr_cl_out                          false
% 2.10/1.01  
% 2.10/1.01  ------ Global Options
% 2.10/1.01  
% 2.10/1.01  --schedule                              default
% 2.10/1.01  --add_important_lit                     false
% 2.10/1.01  --prop_solver_per_cl                    1000
% 2.10/1.01  --min_unsat_core                        false
% 2.10/1.01  --soft_assumptions                      false
% 2.10/1.01  --soft_lemma_size                       3
% 2.10/1.01  --prop_impl_unit_size                   0
% 2.10/1.01  --prop_impl_unit                        []
% 2.10/1.01  --share_sel_clauses                     true
% 2.10/1.01  --reset_solvers                         false
% 2.10/1.01  --bc_imp_inh                            [conj_cone]
% 2.10/1.01  --conj_cone_tolerance                   3.
% 2.10/1.01  --extra_neg_conj                        none
% 2.10/1.01  --large_theory_mode                     true
% 2.10/1.01  --prolific_symb_bound                   200
% 2.10/1.01  --lt_threshold                          2000
% 2.10/1.01  --clause_weak_htbl                      true
% 2.10/1.01  --gc_record_bc_elim                     false
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing Options
% 2.10/1.01  
% 2.10/1.01  --preprocessing_flag                    true
% 2.10/1.01  --time_out_prep_mult                    0.1
% 2.10/1.01  --splitting_mode                        input
% 2.10/1.01  --splitting_grd                         true
% 2.10/1.01  --splitting_cvd                         false
% 2.10/1.01  --splitting_cvd_svl                     false
% 2.10/1.01  --splitting_nvd                         32
% 2.10/1.01  --sub_typing                            true
% 2.10/1.01  --prep_gs_sim                           true
% 2.10/1.01  --prep_unflatten                        true
% 2.10/1.01  --prep_res_sim                          true
% 2.10/1.01  --prep_upred                            true
% 2.10/1.01  --prep_sem_filter                       exhaustive
% 2.10/1.01  --prep_sem_filter_out                   false
% 2.10/1.01  --pred_elim                             true
% 2.10/1.01  --res_sim_input                         true
% 2.10/1.01  --eq_ax_congr_red                       true
% 2.10/1.01  --pure_diseq_elim                       true
% 2.10/1.01  --brand_transform                       false
% 2.10/1.01  --non_eq_to_eq                          false
% 2.10/1.01  --prep_def_merge                        true
% 2.10/1.01  --prep_def_merge_prop_impl              false
% 2.10/1.01  --prep_def_merge_mbd                    true
% 2.10/1.01  --prep_def_merge_tr_red                 false
% 2.10/1.01  --prep_def_merge_tr_cl                  false
% 2.10/1.01  --smt_preprocessing                     true
% 2.10/1.01  --smt_ac_axioms                         fast
% 2.10/1.01  --preprocessed_out                      false
% 2.10/1.01  --preprocessed_stats                    false
% 2.10/1.01  
% 2.10/1.01  ------ Abstraction refinement Options
% 2.10/1.01  
% 2.10/1.01  --abstr_ref                             []
% 2.10/1.01  --abstr_ref_prep                        false
% 2.10/1.01  --abstr_ref_until_sat                   false
% 2.10/1.01  --abstr_ref_sig_restrict                funpre
% 2.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.01  --abstr_ref_under                       []
% 2.10/1.01  
% 2.10/1.01  ------ SAT Options
% 2.10/1.01  
% 2.10/1.01  --sat_mode                              false
% 2.10/1.01  --sat_fm_restart_options                ""
% 2.10/1.01  --sat_gr_def                            false
% 2.10/1.01  --sat_epr_types                         true
% 2.10/1.01  --sat_non_cyclic_types                  false
% 2.10/1.01  --sat_finite_models                     false
% 2.10/1.01  --sat_fm_lemmas                         false
% 2.10/1.01  --sat_fm_prep                           false
% 2.10/1.01  --sat_fm_uc_incr                        true
% 2.10/1.01  --sat_out_model                         small
% 2.10/1.01  --sat_out_clauses                       false
% 2.10/1.01  
% 2.10/1.01  ------ QBF Options
% 2.10/1.01  
% 2.10/1.01  --qbf_mode                              false
% 2.10/1.01  --qbf_elim_univ                         false
% 2.10/1.01  --qbf_dom_inst                          none
% 2.10/1.01  --qbf_dom_pre_inst                      false
% 2.10/1.01  --qbf_sk_in                             false
% 2.10/1.01  --qbf_pred_elim                         true
% 2.10/1.01  --qbf_split                             512
% 2.10/1.01  
% 2.10/1.01  ------ BMC1 Options
% 2.10/1.01  
% 2.10/1.01  --bmc1_incremental                      false
% 2.10/1.01  --bmc1_axioms                           reachable_all
% 2.10/1.01  --bmc1_min_bound                        0
% 2.10/1.01  --bmc1_max_bound                        -1
% 2.10/1.01  --bmc1_max_bound_default                -1
% 2.10/1.01  --bmc1_symbol_reachability              true
% 2.10/1.01  --bmc1_property_lemmas                  false
% 2.10/1.01  --bmc1_k_induction                      false
% 2.10/1.01  --bmc1_non_equiv_states                 false
% 2.10/1.01  --bmc1_deadlock                         false
% 2.10/1.01  --bmc1_ucm                              false
% 2.10/1.01  --bmc1_add_unsat_core                   none
% 2.10/1.01  --bmc1_unsat_core_children              false
% 2.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.01  --bmc1_out_stat                         full
% 2.10/1.01  --bmc1_ground_init                      false
% 2.10/1.01  --bmc1_pre_inst_next_state              false
% 2.10/1.01  --bmc1_pre_inst_state                   false
% 2.10/1.01  --bmc1_pre_inst_reach_state             false
% 2.10/1.01  --bmc1_out_unsat_core                   false
% 2.10/1.01  --bmc1_aig_witness_out                  false
% 2.10/1.01  --bmc1_verbose                          false
% 2.10/1.01  --bmc1_dump_clauses_tptp                false
% 2.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.01  --bmc1_dump_file                        -
% 2.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.01  --bmc1_ucm_extend_mode                  1
% 2.10/1.01  --bmc1_ucm_init_mode                    2
% 2.10/1.01  --bmc1_ucm_cone_mode                    none
% 2.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.01  --bmc1_ucm_relax_model                  4
% 2.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.01  --bmc1_ucm_layered_model                none
% 2.10/1.01  --bmc1_ucm_max_lemma_size               10
% 2.10/1.01  
% 2.10/1.01  ------ AIG Options
% 2.10/1.01  
% 2.10/1.01  --aig_mode                              false
% 2.10/1.01  
% 2.10/1.01  ------ Instantiation Options
% 2.10/1.01  
% 2.10/1.01  --instantiation_flag                    true
% 2.10/1.01  --inst_sos_flag                         false
% 2.10/1.01  --inst_sos_phase                        true
% 2.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.01  --inst_lit_sel_side                     none
% 2.10/1.01  --inst_solver_per_active                1400
% 2.10/1.01  --inst_solver_calls_frac                1.
% 2.10/1.01  --inst_passive_queue_type               priority_queues
% 2.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.01  --inst_passive_queues_freq              [25;2]
% 2.10/1.01  --inst_dismatching                      true
% 2.10/1.01  --inst_eager_unprocessed_to_passive     true
% 2.10/1.01  --inst_prop_sim_given                   true
% 2.10/1.01  --inst_prop_sim_new                     false
% 2.10/1.01  --inst_subs_new                         false
% 2.10/1.01  --inst_eq_res_simp                      false
% 2.10/1.01  --inst_subs_given                       false
% 2.10/1.01  --inst_orphan_elimination               true
% 2.10/1.01  --inst_learning_loop_flag               true
% 2.10/1.01  --inst_learning_start                   3000
% 2.10/1.01  --inst_learning_factor                  2
% 2.10/1.01  --inst_start_prop_sim_after_learn       3
% 2.10/1.01  --inst_sel_renew                        solver
% 2.10/1.01  --inst_lit_activity_flag                true
% 2.10/1.01  --inst_restr_to_given                   false
% 2.10/1.01  --inst_activity_threshold               500
% 2.10/1.01  --inst_out_proof                        true
% 2.10/1.01  
% 2.10/1.01  ------ Resolution Options
% 2.10/1.01  
% 2.10/1.01  --resolution_flag                       false
% 2.10/1.01  --res_lit_sel                           adaptive
% 2.10/1.01  --res_lit_sel_side                      none
% 2.10/1.01  --res_ordering                          kbo
% 2.10/1.01  --res_to_prop_solver                    active
% 2.10/1.01  --res_prop_simpl_new                    false
% 2.10/1.01  --res_prop_simpl_given                  true
% 2.10/1.01  --res_passive_queue_type                priority_queues
% 2.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.01  --res_passive_queues_freq               [15;5]
% 2.10/1.01  --res_forward_subs                      full
% 2.10/1.01  --res_backward_subs                     full
% 2.10/1.01  --res_forward_subs_resolution           true
% 2.10/1.01  --res_backward_subs_resolution          true
% 2.10/1.01  --res_orphan_elimination                true
% 2.10/1.01  --res_time_limit                        2.
% 2.10/1.01  --res_out_proof                         true
% 2.10/1.01  
% 2.10/1.01  ------ Superposition Options
% 2.10/1.01  
% 2.10/1.01  --superposition_flag                    true
% 2.10/1.01  --sup_passive_queue_type                priority_queues
% 2.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.01  --demod_completeness_check              fast
% 2.10/1.01  --demod_use_ground                      true
% 2.10/1.01  --sup_to_prop_solver                    passive
% 2.10/1.01  --sup_prop_simpl_new                    true
% 2.10/1.01  --sup_prop_simpl_given                  true
% 2.10/1.01  --sup_fun_splitting                     false
% 2.10/1.01  --sup_smt_interval                      50000
% 2.10/1.01  
% 2.10/1.01  ------ Superposition Simplification Setup
% 2.10/1.01  
% 2.10/1.01  --sup_indices_passive                   []
% 2.10/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_full_bw                           [BwDemod]
% 2.10/1.01  --sup_immed_triv                        [TrivRules]
% 2.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_immed_bw_main                     []
% 2.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.01  
% 2.10/1.01  ------ Combination Options
% 2.10/1.01  
% 2.10/1.01  --comb_res_mult                         3
% 2.10/1.01  --comb_sup_mult                         2
% 2.10/1.01  --comb_inst_mult                        10
% 2.10/1.01  
% 2.10/1.01  ------ Debug Options
% 2.10/1.01  
% 2.10/1.01  --dbg_backtrace                         false
% 2.10/1.01  --dbg_dump_prop_clauses                 false
% 2.10/1.01  --dbg_dump_prop_clauses_file            -
% 2.10/1.01  --dbg_out_stat                          false
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  ------ Proving...
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  % SZS status Theorem for theBenchmark.p
% 2.10/1.01  
% 2.10/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.10/1.01  
% 2.10/1.01  fof(f10,axiom,(
% 2.10/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f18,plain,(
% 2.10/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.10/1.01    inference(ennf_transformation,[],[f10])).
% 2.10/1.01  
% 2.10/1.01  fof(f19,plain,(
% 2.10/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.10/1.01    inference(flattening,[],[f18])).
% 2.10/1.01  
% 2.10/1.01  fof(f48,plain,(
% 2.10/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.10/1.01    inference(cnf_transformation,[],[f19])).
% 2.10/1.01  
% 2.10/1.01  fof(f11,axiom,(
% 2.10/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f20,plain,(
% 2.10/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.01    inference(ennf_transformation,[],[f11])).
% 2.10/1.01  
% 2.10/1.01  fof(f21,plain,(
% 2.10/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.01    inference(flattening,[],[f20])).
% 2.10/1.01  
% 2.10/1.01  fof(f29,plain,(
% 2.10/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.01    inference(nnf_transformation,[],[f21])).
% 2.10/1.01  
% 2.10/1.01  fof(f51,plain,(
% 2.10/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.01    inference(cnf_transformation,[],[f29])).
% 2.10/1.01  
% 2.10/1.01  fof(f12,conjecture,(
% 2.10/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f13,negated_conjecture,(
% 2.10/1.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.10/1.01    inference(negated_conjecture,[],[f12])).
% 2.10/1.01  
% 2.10/1.01  fof(f22,plain,(
% 2.10/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.10/1.01    inference(ennf_transformation,[],[f13])).
% 2.10/1.01  
% 2.10/1.01  fof(f23,plain,(
% 2.10/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.10/1.01    inference(flattening,[],[f22])).
% 2.10/1.01  
% 2.10/1.01  fof(f30,plain,(
% 2.10/1.01    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.10/1.01    introduced(choice_axiom,[])).
% 2.10/1.01  
% 2.10/1.01  fof(f31,plain,(
% 2.10/1.01    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.10/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f30])).
% 2.10/1.01  
% 2.10/1.01  fof(f57,plain,(
% 2.10/1.01    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 2.10/1.01    inference(cnf_transformation,[],[f31])).
% 2.10/1.01  
% 2.10/1.01  fof(f56,plain,(
% 2.10/1.01    v1_funct_1(sK0)),
% 2.10/1.01    inference(cnf_transformation,[],[f31])).
% 2.10/1.01  
% 2.10/1.01  fof(f9,axiom,(
% 2.10/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f17,plain,(
% 2.10/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.01    inference(ennf_transformation,[],[f9])).
% 2.10/1.01  
% 2.10/1.01  fof(f47,plain,(
% 2.10/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.01    inference(cnf_transformation,[],[f17])).
% 2.10/1.01  
% 2.10/1.01  fof(f55,plain,(
% 2.10/1.01    v1_relat_1(sK0)),
% 2.10/1.01    inference(cnf_transformation,[],[f31])).
% 2.10/1.01  
% 2.10/1.01  fof(f2,axiom,(
% 2.10/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f24,plain,(
% 2.10/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/1.01    inference(nnf_transformation,[],[f2])).
% 2.10/1.01  
% 2.10/1.01  fof(f25,plain,(
% 2.10/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/1.01    inference(flattening,[],[f24])).
% 2.10/1.01  
% 2.10/1.01  fof(f33,plain,(
% 2.10/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.10/1.01    inference(cnf_transformation,[],[f25])).
% 2.10/1.01  
% 2.10/1.01  fof(f59,plain,(
% 2.10/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.10/1.01    inference(equality_resolution,[],[f33])).
% 2.10/1.01  
% 2.10/1.01  fof(f4,axiom,(
% 2.10/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f26,plain,(
% 2.10/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.10/1.01    inference(nnf_transformation,[],[f4])).
% 2.10/1.01  
% 2.10/1.01  fof(f27,plain,(
% 2.10/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.10/1.01    inference(flattening,[],[f26])).
% 2.10/1.01  
% 2.10/1.01  fof(f39,plain,(
% 2.10/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.10/1.01    inference(cnf_transformation,[],[f27])).
% 2.10/1.01  
% 2.10/1.01  fof(f60,plain,(
% 2.10/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.10/1.01    inference(equality_resolution,[],[f39])).
% 2.10/1.01  
% 2.10/1.01  fof(f3,axiom,(
% 2.10/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f36,plain,(
% 2.10/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.10/1.01    inference(cnf_transformation,[],[f3])).
% 2.10/1.01  
% 2.10/1.01  fof(f54,plain,(
% 2.10/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.01    inference(cnf_transformation,[],[f29])).
% 2.10/1.01  
% 2.10/1.01  fof(f62,plain,(
% 2.10/1.01    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.01    inference(equality_resolution,[],[f54])).
% 2.10/1.01  
% 2.10/1.01  fof(f63,plain,(
% 2.10/1.01    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.10/1.01    inference(equality_resolution,[],[f62])).
% 2.10/1.01  
% 2.10/1.01  fof(f5,axiom,(
% 2.10/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f28,plain,(
% 2.10/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.10/1.01    inference(nnf_transformation,[],[f5])).
% 2.10/1.01  
% 2.10/1.01  fof(f41,plain,(
% 2.10/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.10/1.01    inference(cnf_transformation,[],[f28])).
% 2.10/1.01  
% 2.10/1.01  fof(f35,plain,(
% 2.10/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.10/1.01    inference(cnf_transformation,[],[f25])).
% 2.10/1.01  
% 2.10/1.01  fof(f40,plain,(
% 2.10/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.10/1.01    inference(cnf_transformation,[],[f28])).
% 2.10/1.01  
% 2.10/1.01  fof(f7,axiom,(
% 2.10/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.10/1.01  
% 2.10/1.01  fof(f15,plain,(
% 2.10/1.01    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/1.01    inference(ennf_transformation,[],[f7])).
% 2.10/1.01  
% 2.10/1.01  fof(f16,plain,(
% 2.10/1.01    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/1.01    inference(flattening,[],[f15])).
% 2.10/1.01  
% 2.10/1.01  fof(f44,plain,(
% 2.10/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.10/1.01    inference(cnf_transformation,[],[f16])).
% 2.10/1.01  
% 2.10/1.01  fof(f38,plain,(
% 2.10/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.10/1.01    inference(cnf_transformation,[],[f27])).
% 2.10/1.01  
% 2.10/1.01  fof(f61,plain,(
% 2.10/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.10/1.01    inference(equality_resolution,[],[f38])).
% 2.10/1.01  
% 2.10/1.01  fof(f52,plain,(
% 2.10/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.01    inference(cnf_transformation,[],[f29])).
% 2.10/1.01  
% 2.10/1.01  fof(f65,plain,(
% 2.10/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.10/1.01    inference(equality_resolution,[],[f52])).
% 2.10/1.01  
% 2.10/1.01  cnf(c_16,plain,
% 2.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.10/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.10/1.01      | ~ v1_relat_1(X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_910,plain,
% 2.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.10/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.10/1.01      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 2.10/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_20,plain,
% 2.10/1.01      ( v1_funct_2(X0,X1,X2)
% 2.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.01      | k1_relset_1(X1,X2,X0) != X1
% 2.10/1.01      | k1_xboole_0 = X2 ),
% 2.10/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_23,negated_conjecture,
% 2.10/1.01      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 2.10/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | ~ v1_funct_1(sK0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_24,negated_conjecture,
% 2.10/1.01      ( v1_funct_1(sK0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_124,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_23,c_24]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_125,negated_conjecture,
% 2.10/1.01      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 2.10/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_124]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_355,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | k1_relset_1(X1,X2,X0) != X1
% 2.10/1.01      | k1_relat_1(sK0) != X1
% 2.10/1.01      | k2_relat_1(sK0) != X2
% 2.10/1.01      | sK0 != X0
% 2.10/1.01      | k1_xboole_0 = X2 ),
% 2.10/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_125]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_356,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
% 2.10/1.01      | k1_xboole_0 = k2_relat_1(sK0) ),
% 2.10/1.01      inference(unflattening,[status(thm)],[c_355]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_15,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_364,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | k1_xboole_0 = k2_relat_1(sK0) ),
% 2.10/1.01      inference(forward_subsumption_resolution,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_356,c_15]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_905,plain,
% 2.10/1.01      ( k1_xboole_0 = k2_relat_1(sK0)
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1812,plain,
% 2.10/1.01      ( k2_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
% 2.10/1.01      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
% 2.10/1.01      | v1_relat_1(sK0) != iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_910,c_905]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_25,negated_conjecture,
% 2.10/1.01      ( v1_relat_1(sK0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_26,plain,
% 2.10/1.01      ( v1_relat_1(sK0) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_3,plain,
% 2.10/1.01      ( r1_tarski(X0,X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1587,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1590,plain,
% 2.10/1.01      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1587]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2180,plain,
% 2.10/1.01      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
% 2.10/1.01      | k2_relat_1(sK0) = k1_xboole_0 ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_1812,c_26,c_1590]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2181,plain,
% 2.10/1.01      ( k2_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_2180]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_917,plain,
% 2.10/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2186,plain,
% 2.10/1.01      ( k2_relat_1(sK0) = k1_xboole_0 ),
% 2.10/1.01      inference(forward_subsumption_resolution,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_2181,c_917]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_5,plain,
% 2.10/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.10/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1808,plain,
% 2.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.10/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.10/1.01      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 2.10/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_5,c_910]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2997,plain,
% 2.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.10/1.01      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 2.10/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_917,c_1808]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_3615,plain,
% 2.10/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.10/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.10/1.01      | v1_relat_1(sK0) != iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_2186,c_2997]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_4,plain,
% 2.10/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_70,plain,
% 2.10/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_72,plain,
% 2.10/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_70]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_4019,plain,
% 2.10/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_3615,c_26,c_72]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_17,plain,
% 2.10/1.01      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.10/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.10/1.01      | k1_xboole_0 = X0 ),
% 2.10/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_312,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.10/1.01      | k1_relat_1(sK0) != X0
% 2.10/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | k1_xboole_0 = X0 ),
% 2.10/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_125]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_313,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
% 2.10/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | k1_xboole_0 = k1_relat_1(sK0) ),
% 2.10/1.01      inference(unflattening,[status(thm)],[c_312]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_907,plain,
% 2.10/1.01      ( k2_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | k1_xboole_0 = k1_relat_1(sK0)
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.10/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_996,plain,
% 2.10/1.01      ( k1_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.10/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.01      inference(demodulation,[status(thm)],[c_907,c_5]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_8,plain,
% 2.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.10/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_65,plain,
% 2.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.10/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_67,plain,
% 2.10/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.10/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_65]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1067,plain,
% 2.10/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | k1_relat_1(sK0) = k1_xboole_0 ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_996,c_67,c_72]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1068,plain,
% 2.10/1.01      ( k1_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
% 2.10/1.01      inference(renaming,[status(thm)],[c_1067]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2187,plain,
% 2.10/1.01      ( k1_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | k1_xboole_0 != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
% 2.10/1.01      inference(demodulation,[status(thm)],[c_2186,c_1068]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2198,plain,
% 2.10/1.01      ( k1_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
% 2.10/1.01      inference(equality_resolution_simp,[status(thm)],[c_2187]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2202,plain,
% 2.10/1.01      ( k1_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.01      inference(demodulation,[status(thm)],[c_2198,c_5]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_66,plain,
% 2.10/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.10/1.01      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_71,plain,
% 2.10/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1008,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 2.10/1.01      | k1_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | k2_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | sK0 != k1_xboole_0 ),
% 2.10/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_996]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1,plain,
% 2.10/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.10/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1082,plain,
% 2.10/1.01      ( ~ r1_tarski(sK0,k1_xboole_0)
% 2.10/1.01      | ~ r1_tarski(k1_xboole_0,sK0)
% 2.10/1.01      | sK0 = k1_xboole_0 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1083,plain,
% 2.10/1.01      ( sK0 = k1_xboole_0
% 2.10/1.01      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 2.10/1.01      | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1082]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_9,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.10/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1097,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
% 2.10/1.01      | r1_tarski(sK0,k1_xboole_0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1098,plain,
% 2.10/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.10/1.01      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1097]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1463,plain,
% 2.10/1.01      ( r1_tarski(sK0,sK0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1663,plain,
% 2.10/1.01      ( r1_tarski(k1_xboole_0,sK0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1666,plain,
% 2.10/1.01      ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1663]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1056,plain,
% 2.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
% 2.10/1.01      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.10/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.10/1.01      | ~ v1_relat_1(X0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1326,plain,
% 2.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X0))))
% 2.10/1.01      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.10/1.01      | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X0))
% 2.10/1.01      | ~ v1_relat_1(X0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1056]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2124,plain,
% 2.10/1.01      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
% 2.10/1.01      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
% 2.10/1.01      | ~ v1_relat_1(sK0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_1326]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_11,plain,
% 2.10/1.01      ( ~ r1_tarski(X0,X1)
% 2.10/1.01      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.10/1.01      | ~ v1_relat_1(X1)
% 2.10/1.01      | ~ v1_relat_1(X0) ),
% 2.10/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2347,plain,
% 2.10/1.01      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
% 2.10/1.01      | ~ r1_tarski(sK0,sK0)
% 2.10/1.01      | ~ v1_relat_1(sK0) ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2371,plain,
% 2.10/1.01      ( k1_relat_1(sK0) = k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_2202,c_25,c_66,c_71,c_1008,c_1083,c_1098,c_1463,
% 2.10/1.01                 c_1587,c_1666,c_2124,c_2186,c_2347]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_4025,plain,
% 2.10/1.01      ( k1_relat_1(sK0) = k1_xboole_0 ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_4019,c_2371]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_6,plain,
% 2.10/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.10/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_911,plain,
% 2.10/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.10/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_1490,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.10/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_6,c_911]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_4026,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,X0,sK0) = k1_relat_1(sK0) ),
% 2.10/1.01      inference(superposition,[status(thm)],[c_4019,c_1490]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_4033,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,X0,sK0) = k1_xboole_0 ),
% 2.10/1.01      inference(demodulation,[status(thm)],[c_4025,c_4026]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_4040,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) = k1_xboole_0 ),
% 2.10/1.01      inference(instantiation,[status(thm)],[c_4033]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_19,plain,
% 2.10/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.10/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.10/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_339,plain,
% 2.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.10/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.10/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | k2_relat_1(sK0) != X1
% 2.10/1.01      | sK0 != X0 ),
% 2.10/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_125]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_340,plain,
% 2.10/1.01      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.10/1.01      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
% 2.10/1.01      | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.10/1.01      | k1_relat_1(sK0) != k1_xboole_0 ),
% 2.10/1.01      inference(unflattening,[status(thm)],[c_339]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_906,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.10/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
% 2.10/1.01      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_987,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.10/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.01      inference(demodulation,[status(thm)],[c_906,c_6]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2188,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.10/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.01      inference(demodulation,[status(thm)],[c_2186,c_987]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2194,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.10/1.01      | k1_relat_1(sK0) != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.01      inference(demodulation,[status(thm)],[c_2188,c_5]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(c_2364,plain,
% 2.10/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.10/1.01      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.10/1.01      inference(global_propositional_subsumption,
% 2.10/1.01                [status(thm)],
% 2.10/1.01                [c_2194,c_25,c_66,c_71,c_1008,c_1083,c_1098,c_1463,
% 2.10/1.01                 c_1587,c_1666,c_2124,c_2186,c_2347]) ).
% 2.10/1.01  
% 2.10/1.01  cnf(contradiction,plain,
% 2.10/1.01      ( $false ),
% 2.10/1.01      inference(minisat,[status(thm)],[c_4040,c_3615,c_2364,c_72,c_26]) ).
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.10/1.01  
% 2.10/1.01  ------                               Statistics
% 2.10/1.01  
% 2.10/1.01  ------ General
% 2.10/1.01  
% 2.10/1.01  abstr_ref_over_cycles:                  0
% 2.10/1.01  abstr_ref_under_cycles:                 0
% 2.10/1.01  gc_basic_clause_elim:                   0
% 2.10/1.01  forced_gc_time:                         0
% 2.10/1.01  parsing_time:                           0.009
% 2.10/1.01  unif_index_cands_time:                  0.
% 2.10/1.01  unif_index_add_time:                    0.
% 2.10/1.01  orderings_time:                         0.
% 2.10/1.01  out_proof_time:                         0.012
% 2.10/1.01  total_time:                             0.183
% 2.10/1.01  num_of_symbols:                         44
% 2.10/1.01  num_of_terms:                           2881
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing
% 2.10/1.01  
% 2.10/1.01  num_of_splits:                          0
% 2.10/1.01  num_of_split_atoms:                     0
% 2.10/1.01  num_of_reused_defs:                     0
% 2.10/1.01  num_eq_ax_congr_red:                    2
% 2.10/1.01  num_of_sem_filtered_clauses:            2
% 2.10/1.01  num_of_subtypes:                        0
% 2.10/1.01  monotx_restored_types:                  0
% 2.10/1.01  sat_num_of_epr_types:                   0
% 2.10/1.01  sat_num_of_non_cyclic_types:            0
% 2.10/1.01  sat_guarded_non_collapsed_types:        0
% 2.10/1.01  num_pure_diseq_elim:                    0
% 2.10/1.01  simp_replaced_by:                       0
% 2.10/1.01  res_preprocessed:                       103
% 2.10/1.01  prep_upred:                             0
% 2.10/1.01  prep_unflattend:                        27
% 2.10/1.01  smt_new_axioms:                         0
% 2.10/1.01  pred_elim_cands:                        3
% 2.10/1.01  pred_elim:                              2
% 2.10/1.01  pred_elim_cl:                           5
% 2.10/1.01  pred_elim_cycles:                       4
% 2.10/1.01  merged_defs:                            8
% 2.10/1.01  merged_defs_ncl:                        0
% 2.10/1.01  bin_hyper_res:                          8
% 2.10/1.01  prep_cycles:                            4
% 2.10/1.01  pred_elim_time:                         0.002
% 2.10/1.01  splitting_time:                         0.
% 2.10/1.01  sem_filter_time:                        0.
% 2.10/1.01  monotx_time:                            0.
% 2.10/1.01  subtype_inf_time:                       0.
% 2.10/1.01  
% 2.10/1.01  ------ Problem properties
% 2.10/1.01  
% 2.10/1.01  clauses:                                19
% 2.10/1.01  conjectures:                            1
% 2.10/1.01  epr:                                    5
% 2.10/1.01  horn:                                   18
% 2.10/1.01  ground:                                 7
% 2.10/1.01  unary:                                  8
% 2.10/1.01  binary:                                 4
% 2.10/1.01  lits:                                   43
% 2.10/1.01  lits_eq:                                15
% 2.10/1.01  fd_pure:                                0
% 2.10/1.01  fd_pseudo:                              0
% 2.10/1.01  fd_cond:                                1
% 2.10/1.01  fd_pseudo_cond:                         1
% 2.10/1.01  ac_symbols:                             0
% 2.10/1.01  
% 2.10/1.01  ------ Propositional Solver
% 2.10/1.01  
% 2.10/1.01  prop_solver_calls:                      28
% 2.10/1.01  prop_fast_solver_calls:                 677
% 2.10/1.01  smt_solver_calls:                       0
% 2.10/1.01  smt_fast_solver_calls:                  0
% 2.10/1.01  prop_num_of_clauses:                    1240
% 2.10/1.01  prop_preprocess_simplified:             3968
% 2.10/1.01  prop_fo_subsumed:                       14
% 2.10/1.01  prop_solver_time:                       0.
% 2.10/1.01  smt_solver_time:                        0.
% 2.10/1.01  smt_fast_solver_time:                   0.
% 2.10/1.01  prop_fast_solver_time:                  0.
% 2.10/1.01  prop_unsat_core_time:                   0.
% 2.10/1.01  
% 2.10/1.01  ------ QBF
% 2.10/1.01  
% 2.10/1.01  qbf_q_res:                              0
% 2.10/1.01  qbf_num_tautologies:                    0
% 2.10/1.01  qbf_prep_cycles:                        0
% 2.10/1.01  
% 2.10/1.01  ------ BMC1
% 2.10/1.01  
% 2.10/1.01  bmc1_current_bound:                     -1
% 2.10/1.01  bmc1_last_solved_bound:                 -1
% 2.10/1.01  bmc1_unsat_core_size:                   -1
% 2.10/1.01  bmc1_unsat_core_parents_size:           -1
% 2.10/1.01  bmc1_merge_next_fun:                    0
% 2.10/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.10/1.01  
% 2.10/1.01  ------ Instantiation
% 2.10/1.01  
% 2.10/1.01  inst_num_of_clauses:                    370
% 2.10/1.01  inst_num_in_passive:                    26
% 2.10/1.01  inst_num_in_active:                     230
% 2.10/1.01  inst_num_in_unprocessed:                114
% 2.10/1.01  inst_num_of_loops:                      260
% 2.10/1.01  inst_num_of_learning_restarts:          0
% 2.10/1.01  inst_num_moves_active_passive:          27
% 2.10/1.01  inst_lit_activity:                      0
% 2.10/1.01  inst_lit_activity_moves:                0
% 2.10/1.01  inst_num_tautologies:                   0
% 2.10/1.01  inst_num_prop_implied:                  0
% 2.10/1.01  inst_num_existing_simplified:           0
% 2.10/1.01  inst_num_eq_res_simplified:             0
% 2.10/1.01  inst_num_child_elim:                    0
% 2.10/1.01  inst_num_of_dismatching_blockings:      153
% 2.10/1.01  inst_num_of_non_proper_insts:           514
% 2.10/1.01  inst_num_of_duplicates:                 0
% 2.10/1.01  inst_inst_num_from_inst_to_res:         0
% 2.10/1.01  inst_dismatching_checking_time:         0.
% 2.10/1.01  
% 2.10/1.01  ------ Resolution
% 2.10/1.01  
% 2.10/1.01  res_num_of_clauses:                     0
% 2.10/1.01  res_num_in_passive:                     0
% 2.10/1.01  res_num_in_active:                      0
% 2.10/1.01  res_num_of_loops:                       107
% 2.10/1.01  res_forward_subset_subsumed:            64
% 2.10/1.01  res_backward_subset_subsumed:           2
% 2.10/1.01  res_forward_subsumed:                   0
% 2.10/1.01  res_backward_subsumed:                  0
% 2.10/1.01  res_forward_subsumption_resolution:     1
% 2.10/1.01  res_backward_subsumption_resolution:    0
% 2.10/1.01  res_clause_to_clause_subsumption:       398
% 2.10/1.01  res_orphan_elimination:                 0
% 2.10/1.01  res_tautology_del:                      56
% 2.10/1.01  res_num_eq_res_simplified:              0
% 2.10/1.01  res_num_sel_changes:                    0
% 2.10/1.01  res_moves_from_active_to_pass:          0
% 2.10/1.01  
% 2.10/1.01  ------ Superposition
% 2.10/1.01  
% 2.10/1.01  sup_time_total:                         0.
% 2.10/1.01  sup_time_generating:                    0.
% 2.10/1.01  sup_time_sim_full:                      0.
% 2.10/1.01  sup_time_sim_immed:                     0.
% 2.10/1.01  
% 2.10/1.01  sup_num_of_clauses:                     63
% 2.10/1.01  sup_num_in_active:                      43
% 2.10/1.01  sup_num_in_passive:                     20
% 2.10/1.01  sup_num_of_loops:                       51
% 2.10/1.01  sup_fw_superposition:                   81
% 2.10/1.01  sup_bw_superposition:                   29
% 2.10/1.01  sup_immediate_simplified:               38
% 2.10/1.01  sup_given_eliminated:                   3
% 2.10/1.01  comparisons_done:                       0
% 2.10/1.01  comparisons_avoided:                    0
% 2.10/1.01  
% 2.10/1.01  ------ Simplifications
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  sim_fw_subset_subsumed:                 6
% 2.10/1.01  sim_bw_subset_subsumed:                 3
% 2.10/1.01  sim_fw_subsumed:                        18
% 2.10/1.01  sim_bw_subsumed:                        5
% 2.10/1.01  sim_fw_subsumption_res:                 2
% 2.10/1.01  sim_bw_subsumption_res:                 0
% 2.10/1.01  sim_tautology_del:                      11
% 2.10/1.01  sim_eq_tautology_del:                   13
% 2.10/1.01  sim_eq_res_simp:                        1
% 2.10/1.01  sim_fw_demodulated:                     6
% 2.10/1.01  sim_bw_demodulated:                     8
% 2.10/1.01  sim_light_normalised:                   18
% 2.10/1.01  sim_joinable_taut:                      0
% 2.10/1.01  sim_joinable_simp:                      0
% 2.10/1.01  sim_ac_normalised:                      0
% 2.10/1.01  sim_smt_subsumption:                    0
% 2.10/1.01  
%------------------------------------------------------------------------------
