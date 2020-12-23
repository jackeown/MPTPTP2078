%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:59 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  141 (2131 expanded)
%              Number of clauses        :   95 ( 835 expanded)
%              Number of leaves         :   14 ( 366 expanded)
%              Depth                    :   25
%              Number of atoms          :  422 (7993 expanded)
%              Number of equality atoms :  230 (2109 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,
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

fof(f28,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f27])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f18])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f35])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_615,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_209,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK0),X1)
    | ~ r1_tarski(k1_relat_1(sK0),X0) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_611,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK0),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_104,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_19])).

cnf(c_105,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(renaming,[status(thm)],[c_104])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_relat_1(sK0) != X2
    | k1_relat_1(sK0) != X1
    | sK0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_105])).

cnf(c_279,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_287,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_279,c_10])).

cnf(c_608,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_719,plain,
    ( k2_relat_1(sK0) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_608])).

cnf(c_722,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_727,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_743,plain,
    ( k2_relat_1(sK0) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_727])).

cnf(c_992,plain,
    ( k2_relat_1(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_615,c_743])).

cnf(c_1056,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_relat_1(sK0),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_992,c_611])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1554,plain,
    ( r1_tarski(k1_relat_1(sK0),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_614])).

cnf(c_55,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_64,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_390,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_737,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK0),X1)
    | k2_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_739,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_745,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | k2_relat_1(sK0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_743])).

cnf(c_388,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_735,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_763,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_387,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_764,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_772,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_824,plain,
    ( ~ v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_929,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),X0)))
    | ~ r1_tarski(k2_relat_1(sK0),X0)
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_931,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK0),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_389,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_968,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_969,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_968])).

cnf(c_971,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_963,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1349,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),X0)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_1621,plain,
    ( v1_xboole_0(sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1554,c_55,c_0,c_64,c_739,c_745,c_763,c_764,c_772,c_824,c_931,c_971,c_1351])).

cnf(c_617,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1626,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1621,c_617])).

cnf(c_612,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1247,plain,
    ( k1_relset_1(X0,X1,sK0) = k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(sK0),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_612])).

cnf(c_1630,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1626,c_1247])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_860,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_611])).

cnf(c_54,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_56,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_738,plain,
    ( k2_relat_1(sK0) != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_740,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | r1_tarski(k2_relat_1(sK0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_865,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_860,c_56,c_740,c_745,c_772])).

cnf(c_991,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_865])).

cnf(c_1632,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1626,c_991])).

cnf(c_12,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_235,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k2_relat_1(sK0) != k1_xboole_0
    | k1_relat_1(sK0) != X0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_105])).

cnf(c_236,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_610,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_676,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_610,c_5])).

cnf(c_721,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0))))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(sK0),X0) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_771,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_773,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) = iProver_top
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_775,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_781,plain,
    ( sK0 != k1_xboole_0
    | k1_relat_1(sK0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_727,c_745,c_773,c_772,c_775])).

cnf(c_782,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_781])).

cnf(c_1635,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1626,c_782])).

cnf(c_1636,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1635])).

cnf(c_1651,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1632,c_1636])).

cnf(c_1665,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1630,c_1651])).

cnf(c_1682,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_14,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_relat_1(sK0) != X1
    | k1_relat_1(sK0) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_105])).

cnf(c_263,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_609,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_667,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_609,c_6])).

cnf(c_1054,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_992,c_667])).

cnf(c_1067,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1054,c_5])).

cnf(c_1178,plain,
    ( k1_relat_1(sK0) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_991])).

cnf(c_1179,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1178])).

cnf(c_1631,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1626,c_1179])).

cnf(c_1661,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1631,c_1651])).

cnf(c_1662,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1661])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1682,c_1662,c_56])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:31:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.01/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/0.97  
% 2.01/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.01/0.97  
% 2.01/0.97  ------  iProver source info
% 2.01/0.97  
% 2.01/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.01/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.01/0.97  git: non_committed_changes: false
% 2.01/0.97  git: last_make_outside_of_git: false
% 2.01/0.97  
% 2.01/0.97  ------ 
% 2.01/0.97  
% 2.01/0.97  ------ Input Options
% 2.01/0.97  
% 2.01/0.97  --out_options                           all
% 2.01/0.97  --tptp_safe_out                         true
% 2.01/0.97  --problem_path                          ""
% 2.01/0.97  --include_path                          ""
% 2.01/0.97  --clausifier                            res/vclausify_rel
% 2.01/0.97  --clausifier_options                    --mode clausify
% 2.01/0.97  --stdin                                 false
% 2.01/0.97  --stats_out                             all
% 2.01/0.97  
% 2.01/0.97  ------ General Options
% 2.01/0.97  
% 2.01/0.97  --fof                                   false
% 2.01/0.97  --time_out_real                         305.
% 2.01/0.97  --time_out_virtual                      -1.
% 2.01/0.97  --symbol_type_check                     false
% 2.01/0.97  --clausify_out                          false
% 2.01/0.97  --sig_cnt_out                           false
% 2.01/0.97  --trig_cnt_out                          false
% 2.01/0.97  --trig_cnt_out_tolerance                1.
% 2.01/0.97  --trig_cnt_out_sk_spl                   false
% 2.01/0.97  --abstr_cl_out                          false
% 2.01/0.97  
% 2.01/0.97  ------ Global Options
% 2.01/0.97  
% 2.01/0.97  --schedule                              default
% 2.01/0.97  --add_important_lit                     false
% 2.01/0.97  --prop_solver_per_cl                    1000
% 2.01/0.97  --min_unsat_core                        false
% 2.01/0.97  --soft_assumptions                      false
% 2.01/0.97  --soft_lemma_size                       3
% 2.01/0.97  --prop_impl_unit_size                   0
% 2.01/0.97  --prop_impl_unit                        []
% 2.01/0.97  --share_sel_clauses                     true
% 2.01/0.97  --reset_solvers                         false
% 2.01/0.97  --bc_imp_inh                            [conj_cone]
% 2.01/0.97  --conj_cone_tolerance                   3.
% 2.01/0.97  --extra_neg_conj                        none
% 2.01/0.97  --large_theory_mode                     true
% 2.01/0.97  --prolific_symb_bound                   200
% 2.01/0.97  --lt_threshold                          2000
% 2.01/0.97  --clause_weak_htbl                      true
% 2.01/0.97  --gc_record_bc_elim                     false
% 2.01/0.97  
% 2.01/0.97  ------ Preprocessing Options
% 2.01/0.97  
% 2.01/0.97  --preprocessing_flag                    true
% 2.01/0.97  --time_out_prep_mult                    0.1
% 2.01/0.97  --splitting_mode                        input
% 2.01/0.97  --splitting_grd                         true
% 2.01/0.97  --splitting_cvd                         false
% 2.01/0.97  --splitting_cvd_svl                     false
% 2.01/0.97  --splitting_nvd                         32
% 2.01/0.97  --sub_typing                            true
% 2.01/0.97  --prep_gs_sim                           true
% 2.01/0.97  --prep_unflatten                        true
% 2.01/0.97  --prep_res_sim                          true
% 2.01/0.97  --prep_upred                            true
% 2.01/0.97  --prep_sem_filter                       exhaustive
% 2.01/0.97  --prep_sem_filter_out                   false
% 2.01/0.97  --pred_elim                             true
% 2.01/0.97  --res_sim_input                         true
% 2.01/0.97  --eq_ax_congr_red                       true
% 2.01/0.97  --pure_diseq_elim                       true
% 2.01/0.97  --brand_transform                       false
% 2.01/0.97  --non_eq_to_eq                          false
% 2.01/0.97  --prep_def_merge                        true
% 2.01/0.97  --prep_def_merge_prop_impl              false
% 2.01/0.97  --prep_def_merge_mbd                    true
% 2.01/0.97  --prep_def_merge_tr_red                 false
% 2.01/0.97  --prep_def_merge_tr_cl                  false
% 2.01/0.97  --smt_preprocessing                     true
% 2.01/0.97  --smt_ac_axioms                         fast
% 2.01/0.97  --preprocessed_out                      false
% 2.01/0.97  --preprocessed_stats                    false
% 2.01/0.97  
% 2.01/0.97  ------ Abstraction refinement Options
% 2.01/0.97  
% 2.01/0.97  --abstr_ref                             []
% 2.01/0.97  --abstr_ref_prep                        false
% 2.01/0.97  --abstr_ref_until_sat                   false
% 2.01/0.97  --abstr_ref_sig_restrict                funpre
% 2.01/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/0.97  --abstr_ref_under                       []
% 2.01/0.97  
% 2.01/0.97  ------ SAT Options
% 2.01/0.97  
% 2.01/0.97  --sat_mode                              false
% 2.01/0.97  --sat_fm_restart_options                ""
% 2.01/0.97  --sat_gr_def                            false
% 2.01/0.97  --sat_epr_types                         true
% 2.01/0.97  --sat_non_cyclic_types                  false
% 2.01/0.97  --sat_finite_models                     false
% 2.01/0.97  --sat_fm_lemmas                         false
% 2.01/0.97  --sat_fm_prep                           false
% 2.01/0.97  --sat_fm_uc_incr                        true
% 2.01/0.97  --sat_out_model                         small
% 2.01/0.97  --sat_out_clauses                       false
% 2.01/0.97  
% 2.01/0.97  ------ QBF Options
% 2.01/0.97  
% 2.01/0.97  --qbf_mode                              false
% 2.01/0.97  --qbf_elim_univ                         false
% 2.01/0.97  --qbf_dom_inst                          none
% 2.01/0.97  --qbf_dom_pre_inst                      false
% 2.01/0.97  --qbf_sk_in                             false
% 2.01/0.97  --qbf_pred_elim                         true
% 2.01/0.97  --qbf_split                             512
% 2.01/0.97  
% 2.01/0.97  ------ BMC1 Options
% 2.01/0.97  
% 2.01/0.97  --bmc1_incremental                      false
% 2.01/0.97  --bmc1_axioms                           reachable_all
% 2.01/0.97  --bmc1_min_bound                        0
% 2.01/0.97  --bmc1_max_bound                        -1
% 2.01/0.97  --bmc1_max_bound_default                -1
% 2.01/0.97  --bmc1_symbol_reachability              true
% 2.01/0.97  --bmc1_property_lemmas                  false
% 2.01/0.97  --bmc1_k_induction                      false
% 2.01/0.97  --bmc1_non_equiv_states                 false
% 2.01/0.97  --bmc1_deadlock                         false
% 2.01/0.97  --bmc1_ucm                              false
% 2.01/0.97  --bmc1_add_unsat_core                   none
% 2.01/0.97  --bmc1_unsat_core_children              false
% 2.01/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/0.97  --bmc1_out_stat                         full
% 2.01/0.97  --bmc1_ground_init                      false
% 2.01/0.97  --bmc1_pre_inst_next_state              false
% 2.01/0.97  --bmc1_pre_inst_state                   false
% 2.01/0.97  --bmc1_pre_inst_reach_state             false
% 2.01/0.97  --bmc1_out_unsat_core                   false
% 2.01/0.97  --bmc1_aig_witness_out                  false
% 2.01/0.97  --bmc1_verbose                          false
% 2.01/0.97  --bmc1_dump_clauses_tptp                false
% 2.01/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.01/0.97  --bmc1_dump_file                        -
% 2.01/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.01/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.01/0.97  --bmc1_ucm_extend_mode                  1
% 2.01/0.97  --bmc1_ucm_init_mode                    2
% 2.01/0.97  --bmc1_ucm_cone_mode                    none
% 2.01/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.01/0.97  --bmc1_ucm_relax_model                  4
% 2.01/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.01/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/0.97  --bmc1_ucm_layered_model                none
% 2.01/0.97  --bmc1_ucm_max_lemma_size               10
% 2.01/0.97  
% 2.01/0.97  ------ AIG Options
% 2.01/0.97  
% 2.01/0.97  --aig_mode                              false
% 2.01/0.97  
% 2.01/0.97  ------ Instantiation Options
% 2.01/0.97  
% 2.01/0.97  --instantiation_flag                    true
% 2.01/0.97  --inst_sos_flag                         false
% 2.01/0.97  --inst_sos_phase                        true
% 2.01/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/0.97  --inst_lit_sel_side                     num_symb
% 2.01/0.97  --inst_solver_per_active                1400
% 2.01/0.97  --inst_solver_calls_frac                1.
% 2.01/0.97  --inst_passive_queue_type               priority_queues
% 2.01/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/0.97  --inst_passive_queues_freq              [25;2]
% 2.01/0.97  --inst_dismatching                      true
% 2.01/0.97  --inst_eager_unprocessed_to_passive     true
% 2.01/0.97  --inst_prop_sim_given                   true
% 2.01/0.97  --inst_prop_sim_new                     false
% 2.01/0.97  --inst_subs_new                         false
% 2.01/0.97  --inst_eq_res_simp                      false
% 2.01/0.97  --inst_subs_given                       false
% 2.01/0.97  --inst_orphan_elimination               true
% 2.01/0.97  --inst_learning_loop_flag               true
% 2.01/0.97  --inst_learning_start                   3000
% 2.01/0.97  --inst_learning_factor                  2
% 2.01/0.97  --inst_start_prop_sim_after_learn       3
% 2.01/0.97  --inst_sel_renew                        solver
% 2.01/0.97  --inst_lit_activity_flag                true
% 2.01/0.97  --inst_restr_to_given                   false
% 2.01/0.97  --inst_activity_threshold               500
% 2.01/0.97  --inst_out_proof                        true
% 2.01/0.97  
% 2.01/0.97  ------ Resolution Options
% 2.01/0.97  
% 2.01/0.97  --resolution_flag                       true
% 2.01/0.97  --res_lit_sel                           adaptive
% 2.01/0.97  --res_lit_sel_side                      none
% 2.01/0.97  --res_ordering                          kbo
% 2.01/0.97  --res_to_prop_solver                    active
% 2.01/0.97  --res_prop_simpl_new                    false
% 2.01/0.97  --res_prop_simpl_given                  true
% 2.01/0.97  --res_passive_queue_type                priority_queues
% 2.01/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/0.97  --res_passive_queues_freq               [15;5]
% 2.01/0.97  --res_forward_subs                      full
% 2.01/0.97  --res_backward_subs                     full
% 2.01/0.97  --res_forward_subs_resolution           true
% 2.01/0.97  --res_backward_subs_resolution          true
% 2.01/0.97  --res_orphan_elimination                true
% 2.01/0.97  --res_time_limit                        2.
% 2.01/0.97  --res_out_proof                         true
% 2.01/0.97  
% 2.01/0.97  ------ Superposition Options
% 2.01/0.97  
% 2.01/0.97  --superposition_flag                    true
% 2.01/0.97  --sup_passive_queue_type                priority_queues
% 2.01/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.01/0.97  --demod_completeness_check              fast
% 2.01/0.97  --demod_use_ground                      true
% 2.01/0.97  --sup_to_prop_solver                    passive
% 2.01/0.97  --sup_prop_simpl_new                    true
% 2.01/0.97  --sup_prop_simpl_given                  true
% 2.01/0.97  --sup_fun_splitting                     false
% 2.01/0.97  --sup_smt_interval                      50000
% 2.01/0.97  
% 2.01/0.97  ------ Superposition Simplification Setup
% 2.01/0.97  
% 2.01/0.97  --sup_indices_passive                   []
% 2.01/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_full_bw                           [BwDemod]
% 2.01/0.97  --sup_immed_triv                        [TrivRules]
% 2.01/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_immed_bw_main                     []
% 2.01/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.97  
% 2.01/0.97  ------ Combination Options
% 2.01/0.97  
% 2.01/0.97  --comb_res_mult                         3
% 2.01/0.97  --comb_sup_mult                         2
% 2.01/0.97  --comb_inst_mult                        10
% 2.01/0.97  
% 2.01/0.97  ------ Debug Options
% 2.01/0.97  
% 2.01/0.97  --dbg_backtrace                         false
% 2.01/0.97  --dbg_dump_prop_clauses                 false
% 2.01/0.97  --dbg_dump_prop_clauses_file            -
% 2.01/0.97  --dbg_out_stat                          false
% 2.01/0.97  ------ Parsing...
% 2.01/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.01/0.97  
% 2.01/0.97  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.01/0.97  
% 2.01/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.01/0.97  
% 2.01/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.01/0.97  ------ Proving...
% 2.01/0.97  ------ Problem Properties 
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  clauses                                 14
% 2.01/0.97  conjectures                             0
% 2.01/0.97  EPR                                     4
% 2.01/0.97  Horn                                    13
% 2.01/0.97  unary                                   4
% 2.01/0.97  binary                                  4
% 2.01/0.97  lits                                    33
% 2.01/0.97  lits eq                                 14
% 2.01/0.97  fd_pure                                 0
% 2.01/0.97  fd_pseudo                               0
% 2.01/0.97  fd_cond                                 2
% 2.01/0.97  fd_pseudo_cond                          1
% 2.01/0.97  AC symbols                              0
% 2.01/0.97  
% 2.01/0.97  ------ Schedule dynamic 5 is on 
% 2.01/0.97  
% 2.01/0.97  ------ no conjectures: strip conj schedule 
% 2.01/0.97  
% 2.01/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  ------ 
% 2.01/0.97  Current options:
% 2.01/0.97  ------ 
% 2.01/0.97  
% 2.01/0.97  ------ Input Options
% 2.01/0.97  
% 2.01/0.97  --out_options                           all
% 2.01/0.97  --tptp_safe_out                         true
% 2.01/0.97  --problem_path                          ""
% 2.01/0.97  --include_path                          ""
% 2.01/0.97  --clausifier                            res/vclausify_rel
% 2.01/0.97  --clausifier_options                    --mode clausify
% 2.01/0.97  --stdin                                 false
% 2.01/0.97  --stats_out                             all
% 2.01/0.97  
% 2.01/0.97  ------ General Options
% 2.01/0.97  
% 2.01/0.97  --fof                                   false
% 2.01/0.97  --time_out_real                         305.
% 2.01/0.97  --time_out_virtual                      -1.
% 2.01/0.97  --symbol_type_check                     false
% 2.01/0.97  --clausify_out                          false
% 2.01/0.97  --sig_cnt_out                           false
% 2.01/0.97  --trig_cnt_out                          false
% 2.01/0.97  --trig_cnt_out_tolerance                1.
% 2.01/0.97  --trig_cnt_out_sk_spl                   false
% 2.01/0.97  --abstr_cl_out                          false
% 2.01/0.97  
% 2.01/0.97  ------ Global Options
% 2.01/0.97  
% 2.01/0.97  --schedule                              default
% 2.01/0.97  --add_important_lit                     false
% 2.01/0.97  --prop_solver_per_cl                    1000
% 2.01/0.97  --min_unsat_core                        false
% 2.01/0.97  --soft_assumptions                      false
% 2.01/0.97  --soft_lemma_size                       3
% 2.01/0.97  --prop_impl_unit_size                   0
% 2.01/0.97  --prop_impl_unit                        []
% 2.01/0.97  --share_sel_clauses                     true
% 2.01/0.97  --reset_solvers                         false
% 2.01/0.97  --bc_imp_inh                            [conj_cone]
% 2.01/0.97  --conj_cone_tolerance                   3.
% 2.01/0.97  --extra_neg_conj                        none
% 2.01/0.97  --large_theory_mode                     true
% 2.01/0.97  --prolific_symb_bound                   200
% 2.01/0.97  --lt_threshold                          2000
% 2.01/0.97  --clause_weak_htbl                      true
% 2.01/0.97  --gc_record_bc_elim                     false
% 2.01/0.97  
% 2.01/0.97  ------ Preprocessing Options
% 2.01/0.97  
% 2.01/0.97  --preprocessing_flag                    true
% 2.01/0.97  --time_out_prep_mult                    0.1
% 2.01/0.97  --splitting_mode                        input
% 2.01/0.97  --splitting_grd                         true
% 2.01/0.97  --splitting_cvd                         false
% 2.01/0.97  --splitting_cvd_svl                     false
% 2.01/0.97  --splitting_nvd                         32
% 2.01/0.97  --sub_typing                            true
% 2.01/0.97  --prep_gs_sim                           true
% 2.01/0.97  --prep_unflatten                        true
% 2.01/0.97  --prep_res_sim                          true
% 2.01/0.97  --prep_upred                            true
% 2.01/0.97  --prep_sem_filter                       exhaustive
% 2.01/0.97  --prep_sem_filter_out                   false
% 2.01/0.97  --pred_elim                             true
% 2.01/0.97  --res_sim_input                         true
% 2.01/0.97  --eq_ax_congr_red                       true
% 2.01/0.97  --pure_diseq_elim                       true
% 2.01/0.97  --brand_transform                       false
% 2.01/0.97  --non_eq_to_eq                          false
% 2.01/0.97  --prep_def_merge                        true
% 2.01/0.97  --prep_def_merge_prop_impl              false
% 2.01/0.97  --prep_def_merge_mbd                    true
% 2.01/0.97  --prep_def_merge_tr_red                 false
% 2.01/0.97  --prep_def_merge_tr_cl                  false
% 2.01/0.97  --smt_preprocessing                     true
% 2.01/0.97  --smt_ac_axioms                         fast
% 2.01/0.97  --preprocessed_out                      false
% 2.01/0.97  --preprocessed_stats                    false
% 2.01/0.97  
% 2.01/0.97  ------ Abstraction refinement Options
% 2.01/0.97  
% 2.01/0.97  --abstr_ref                             []
% 2.01/0.97  --abstr_ref_prep                        false
% 2.01/0.97  --abstr_ref_until_sat                   false
% 2.01/0.97  --abstr_ref_sig_restrict                funpre
% 2.01/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/0.97  --abstr_ref_under                       []
% 2.01/0.97  
% 2.01/0.97  ------ SAT Options
% 2.01/0.97  
% 2.01/0.97  --sat_mode                              false
% 2.01/0.97  --sat_fm_restart_options                ""
% 2.01/0.97  --sat_gr_def                            false
% 2.01/0.97  --sat_epr_types                         true
% 2.01/0.97  --sat_non_cyclic_types                  false
% 2.01/0.97  --sat_finite_models                     false
% 2.01/0.97  --sat_fm_lemmas                         false
% 2.01/0.97  --sat_fm_prep                           false
% 2.01/0.97  --sat_fm_uc_incr                        true
% 2.01/0.97  --sat_out_model                         small
% 2.01/0.97  --sat_out_clauses                       false
% 2.01/0.97  
% 2.01/0.97  ------ QBF Options
% 2.01/0.97  
% 2.01/0.97  --qbf_mode                              false
% 2.01/0.97  --qbf_elim_univ                         false
% 2.01/0.97  --qbf_dom_inst                          none
% 2.01/0.97  --qbf_dom_pre_inst                      false
% 2.01/0.97  --qbf_sk_in                             false
% 2.01/0.97  --qbf_pred_elim                         true
% 2.01/0.97  --qbf_split                             512
% 2.01/0.97  
% 2.01/0.97  ------ BMC1 Options
% 2.01/0.97  
% 2.01/0.97  --bmc1_incremental                      false
% 2.01/0.97  --bmc1_axioms                           reachable_all
% 2.01/0.97  --bmc1_min_bound                        0
% 2.01/0.97  --bmc1_max_bound                        -1
% 2.01/0.97  --bmc1_max_bound_default                -1
% 2.01/0.97  --bmc1_symbol_reachability              true
% 2.01/0.97  --bmc1_property_lemmas                  false
% 2.01/0.97  --bmc1_k_induction                      false
% 2.01/0.97  --bmc1_non_equiv_states                 false
% 2.01/0.97  --bmc1_deadlock                         false
% 2.01/0.97  --bmc1_ucm                              false
% 2.01/0.97  --bmc1_add_unsat_core                   none
% 2.01/0.97  --bmc1_unsat_core_children              false
% 2.01/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/0.97  --bmc1_out_stat                         full
% 2.01/0.97  --bmc1_ground_init                      false
% 2.01/0.97  --bmc1_pre_inst_next_state              false
% 2.01/0.97  --bmc1_pre_inst_state                   false
% 2.01/0.97  --bmc1_pre_inst_reach_state             false
% 2.01/0.97  --bmc1_out_unsat_core                   false
% 2.01/0.97  --bmc1_aig_witness_out                  false
% 2.01/0.97  --bmc1_verbose                          false
% 2.01/0.97  --bmc1_dump_clauses_tptp                false
% 2.01/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.01/0.97  --bmc1_dump_file                        -
% 2.01/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.01/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.01/0.97  --bmc1_ucm_extend_mode                  1
% 2.01/0.97  --bmc1_ucm_init_mode                    2
% 2.01/0.97  --bmc1_ucm_cone_mode                    none
% 2.01/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.01/0.97  --bmc1_ucm_relax_model                  4
% 2.01/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.01/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/0.97  --bmc1_ucm_layered_model                none
% 2.01/0.97  --bmc1_ucm_max_lemma_size               10
% 2.01/0.97  
% 2.01/0.97  ------ AIG Options
% 2.01/0.97  
% 2.01/0.97  --aig_mode                              false
% 2.01/0.97  
% 2.01/0.97  ------ Instantiation Options
% 2.01/0.97  
% 2.01/0.97  --instantiation_flag                    true
% 2.01/0.97  --inst_sos_flag                         false
% 2.01/0.97  --inst_sos_phase                        true
% 2.01/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/0.97  --inst_lit_sel_side                     none
% 2.01/0.97  --inst_solver_per_active                1400
% 2.01/0.97  --inst_solver_calls_frac                1.
% 2.01/0.97  --inst_passive_queue_type               priority_queues
% 2.01/0.97  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.01/0.97  --inst_passive_queues_freq              [25;2]
% 2.01/0.97  --inst_dismatching                      true
% 2.01/0.97  --inst_eager_unprocessed_to_passive     true
% 2.01/0.97  --inst_prop_sim_given                   true
% 2.01/0.97  --inst_prop_sim_new                     false
% 2.01/0.97  --inst_subs_new                         false
% 2.01/0.97  --inst_eq_res_simp                      false
% 2.01/0.97  --inst_subs_given                       false
% 2.01/0.97  --inst_orphan_elimination               true
% 2.01/0.97  --inst_learning_loop_flag               true
% 2.01/0.97  --inst_learning_start                   3000
% 2.01/0.97  --inst_learning_factor                  2
% 2.01/0.97  --inst_start_prop_sim_after_learn       3
% 2.01/0.97  --inst_sel_renew                        solver
% 2.01/0.97  --inst_lit_activity_flag                true
% 2.01/0.97  --inst_restr_to_given                   false
% 2.01/0.97  --inst_activity_threshold               500
% 2.01/0.97  --inst_out_proof                        true
% 2.01/0.97  
% 2.01/0.97  ------ Resolution Options
% 2.01/0.97  
% 2.01/0.97  --resolution_flag                       false
% 2.01/0.97  --res_lit_sel                           adaptive
% 2.01/0.97  --res_lit_sel_side                      none
% 2.01/0.97  --res_ordering                          kbo
% 2.01/0.97  --res_to_prop_solver                    active
% 2.01/0.97  --res_prop_simpl_new                    false
% 2.01/0.97  --res_prop_simpl_given                  true
% 2.01/0.97  --res_passive_queue_type                priority_queues
% 2.01/0.97  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.01/0.97  --res_passive_queues_freq               [15;5]
% 2.01/0.97  --res_forward_subs                      full
% 2.01/0.97  --res_backward_subs                     full
% 2.01/0.97  --res_forward_subs_resolution           true
% 2.01/0.97  --res_backward_subs_resolution          true
% 2.01/0.97  --res_orphan_elimination                true
% 2.01/0.97  --res_time_limit                        2.
% 2.01/0.97  --res_out_proof                         true
% 2.01/0.97  
% 2.01/0.97  ------ Superposition Options
% 2.01/0.97  
% 2.01/0.97  --superposition_flag                    true
% 2.01/0.97  --sup_passive_queue_type                priority_queues
% 2.01/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.01/0.97  --demod_completeness_check              fast
% 2.01/0.97  --demod_use_ground                      true
% 2.01/0.97  --sup_to_prop_solver                    passive
% 2.01/0.97  --sup_prop_simpl_new                    true
% 2.01/0.97  --sup_prop_simpl_given                  true
% 2.01/0.97  --sup_fun_splitting                     false
% 2.01/0.97  --sup_smt_interval                      50000
% 2.01/0.97  
% 2.01/0.97  ------ Superposition Simplification Setup
% 2.01/0.97  
% 2.01/0.97  --sup_indices_passive                   []
% 2.01/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_full_bw                           [BwDemod]
% 2.01/0.97  --sup_immed_triv                        [TrivRules]
% 2.01/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_immed_bw_main                     []
% 2.01/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.97  
% 2.01/0.97  ------ Combination Options
% 2.01/0.97  
% 2.01/0.97  --comb_res_mult                         3
% 2.01/0.97  --comb_sup_mult                         2
% 2.01/0.97  --comb_inst_mult                        10
% 2.01/0.97  
% 2.01/0.97  ------ Debug Options
% 2.01/0.97  
% 2.01/0.97  --dbg_backtrace                         false
% 2.01/0.97  --dbg_dump_prop_clauses                 false
% 2.01/0.97  --dbg_dump_prop_clauses_file            -
% 2.01/0.97  --dbg_out_stat                          false
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  ------ Proving...
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  % SZS status Theorem for theBenchmark.p
% 2.01/0.97  
% 2.01/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.01/0.97  
% 2.01/0.97  fof(f3,axiom,(
% 2.01/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f22,plain,(
% 2.01/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.97    inference(nnf_transformation,[],[f3])).
% 2.01/0.97  
% 2.01/0.97  fof(f23,plain,(
% 2.01/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.97    inference(flattening,[],[f22])).
% 2.01/0.97  
% 2.01/0.97  fof(f31,plain,(
% 2.01/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.01/0.97    inference(cnf_transformation,[],[f23])).
% 2.01/0.97  
% 2.01/0.97  fof(f51,plain,(
% 2.01/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.01/0.97    inference(equality_resolution,[],[f31])).
% 2.01/0.97  
% 2.01/0.97  fof(f8,axiom,(
% 2.01/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f16,plain,(
% 2.01/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.01/0.97    inference(ennf_transformation,[],[f8])).
% 2.01/0.97  
% 2.01/0.97  fof(f17,plain,(
% 2.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.01/0.97    inference(flattening,[],[f16])).
% 2.01/0.97  
% 2.01/0.97  fof(f40,plain,(
% 2.01/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f17])).
% 2.01/0.97  
% 2.01/0.97  fof(f10,conjecture,(
% 2.01/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f11,negated_conjecture,(
% 2.01/0.97    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.01/0.97    inference(negated_conjecture,[],[f10])).
% 2.01/0.97  
% 2.01/0.97  fof(f20,plain,(
% 2.01/0.97    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.01/0.97    inference(ennf_transformation,[],[f11])).
% 2.01/0.97  
% 2.01/0.97  fof(f21,plain,(
% 2.01/0.97    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.01/0.97    inference(flattening,[],[f20])).
% 2.01/0.97  
% 2.01/0.97  fof(f27,plain,(
% 2.01/0.97    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.01/0.97    introduced(choice_axiom,[])).
% 2.01/0.97  
% 2.01/0.97  fof(f28,plain,(
% 2.01/0.97    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f27])).
% 2.01/0.97  
% 2.01/0.97  fof(f47,plain,(
% 2.01/0.97    v1_relat_1(sK0)),
% 2.01/0.97    inference(cnf_transformation,[],[f28])).
% 2.01/0.97  
% 2.01/0.97  fof(f9,axiom,(
% 2.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f18,plain,(
% 2.01/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.97    inference(ennf_transformation,[],[f9])).
% 2.01/0.97  
% 2.01/0.97  fof(f19,plain,(
% 2.01/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.97    inference(flattening,[],[f18])).
% 2.01/0.97  
% 2.01/0.97  fof(f26,plain,(
% 2.01/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.97    inference(nnf_transformation,[],[f19])).
% 2.01/0.97  
% 2.01/0.97  fof(f43,plain,(
% 2.01/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/0.97    inference(cnf_transformation,[],[f26])).
% 2.01/0.97  
% 2.01/0.97  fof(f49,plain,(
% 2.01/0.97    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 2.01/0.97    inference(cnf_transformation,[],[f28])).
% 2.01/0.97  
% 2.01/0.97  fof(f48,plain,(
% 2.01/0.97    v1_funct_1(sK0)),
% 2.01/0.97    inference(cnf_transformation,[],[f28])).
% 2.01/0.97  
% 2.01/0.97  fof(f7,axiom,(
% 2.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f15,plain,(
% 2.01/0.97    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.97    inference(ennf_transformation,[],[f7])).
% 2.01/0.97  
% 2.01/0.97  fof(f39,plain,(
% 2.01/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/0.97    inference(cnf_transformation,[],[f15])).
% 2.01/0.97  
% 2.01/0.97  fof(f5,axiom,(
% 2.01/0.97    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f13,plain,(
% 2.01/0.97    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.01/0.97    inference(ennf_transformation,[],[f5])).
% 2.01/0.97  
% 2.01/0.97  fof(f37,plain,(
% 2.01/0.97    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f13])).
% 2.01/0.97  
% 2.01/0.97  fof(f1,axiom,(
% 2.01/0.97    v1_xboole_0(k1_xboole_0)),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f29,plain,(
% 2.01/0.97    v1_xboole_0(k1_xboole_0)),
% 2.01/0.97    inference(cnf_transformation,[],[f1])).
% 2.01/0.97  
% 2.01/0.97  fof(f2,axiom,(
% 2.01/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f12,plain,(
% 2.01/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.01/0.97    inference(ennf_transformation,[],[f2])).
% 2.01/0.97  
% 2.01/0.97  fof(f30,plain,(
% 2.01/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.01/0.97    inference(cnf_transformation,[],[f12])).
% 2.01/0.97  
% 2.01/0.97  fof(f4,axiom,(
% 2.01/0.97    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.01/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.01/0.97  
% 2.01/0.97  fof(f24,plain,(
% 2.01/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.01/0.97    inference(nnf_transformation,[],[f4])).
% 2.01/0.97  
% 2.01/0.97  fof(f25,plain,(
% 2.01/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.01/0.97    inference(flattening,[],[f24])).
% 2.01/0.97  
% 2.01/0.97  fof(f36,plain,(
% 2.01/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.01/0.97    inference(cnf_transformation,[],[f25])).
% 2.01/0.97  
% 2.01/0.97  fof(f52,plain,(
% 2.01/0.97    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.01/0.97    inference(equality_resolution,[],[f36])).
% 2.01/0.97  
% 2.01/0.97  fof(f46,plain,(
% 2.01/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/0.97    inference(cnf_transformation,[],[f26])).
% 2.01/0.97  
% 2.01/0.97  fof(f54,plain,(
% 2.01/0.97    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/0.97    inference(equality_resolution,[],[f46])).
% 2.01/0.97  
% 2.01/0.97  fof(f55,plain,(
% 2.01/0.97    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.01/0.97    inference(equality_resolution,[],[f54])).
% 2.01/0.97  
% 2.01/0.97  fof(f44,plain,(
% 2.01/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/0.97    inference(cnf_transformation,[],[f26])).
% 2.01/0.97  
% 2.01/0.97  fof(f57,plain,(
% 2.01/0.97    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.01/0.97    inference(equality_resolution,[],[f44])).
% 2.01/0.97  
% 2.01/0.97  fof(f35,plain,(
% 2.01/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.01/0.97    inference(cnf_transformation,[],[f25])).
% 2.01/0.97  
% 2.01/0.97  fof(f53,plain,(
% 2.01/0.97    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.01/0.97    inference(equality_resolution,[],[f35])).
% 2.01/0.97  
% 2.01/0.97  cnf(c_4,plain,
% 2.01/0.97      ( r1_tarski(X0,X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_615,plain,
% 2.01/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_11,plain,
% 2.01/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/0.97      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.01/0.97      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.01/0.97      | ~ v1_relat_1(X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_20,negated_conjecture,
% 2.01/0.97      ( v1_relat_1(sK0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_208,plain,
% 2.01/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/0.97      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.01/0.97      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.01/0.97      | sK0 != X0 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_209,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.01/0.97      | ~ r1_tarski(k2_relat_1(sK0),X1)
% 2.01/0.97      | ~ r1_tarski(k1_relat_1(sK0),X0) ),
% 2.01/0.97      inference(unflattening,[status(thm)],[c_208]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_611,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.01/0.97      | r1_tarski(k2_relat_1(sK0),X1) != iProver_top
% 2.01/0.97      | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_15,plain,
% 2.01/0.97      ( v1_funct_2(X0,X1,X2)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/0.97      | k1_relset_1(X1,X2,X0) != X1
% 2.01/0.97      | k1_xboole_0 = X2 ),
% 2.01/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_18,negated_conjecture,
% 2.01/0.97      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 2.01/0.97      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | ~ v1_funct_1(sK0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_19,negated_conjecture,
% 2.01/0.97      ( v1_funct_1(sK0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_104,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_18,c_19]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_105,negated_conjecture,
% 2.01/0.97      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 2.01/0.97      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
% 2.01/0.97      inference(renaming,[status(thm)],[c_104]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_278,plain,
% 2.01/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/0.97      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | k1_relset_1(X1,X2,X0) != X1
% 2.01/0.97      | k2_relat_1(sK0) != X2
% 2.01/0.97      | k1_relat_1(sK0) != X1
% 2.01/0.97      | sK0 != X0
% 2.01/0.97      | k1_xboole_0 = X2 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_105]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_279,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
% 2.01/0.97      | k1_xboole_0 = k2_relat_1(sK0) ),
% 2.01/0.97      inference(unflattening,[status(thm)],[c_278]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_10,plain,
% 2.01/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_287,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | k1_xboole_0 = k2_relat_1(sK0) ),
% 2.01/0.97      inference(forward_subsumption_resolution,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_279,c_10]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_608,plain,
% 2.01/0.97      ( k1_xboole_0 = k2_relat_1(sK0)
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_719,plain,
% 2.01/0.97      ( k2_relat_1(sK0) = k1_xboole_0
% 2.01/0.97      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
% 2.01/0.97      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_611,c_608]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_722,plain,
% 2.01/0.97      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_727,plain,
% 2.01/0.97      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_743,plain,
% 2.01/0.97      ( k2_relat_1(sK0) = k1_xboole_0
% 2.01/0.97      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_719,c_727]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_992,plain,
% 2.01/0.97      ( k2_relat_1(sK0) = k1_xboole_0 ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_615,c_743]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1056,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.01/0.97      | r1_tarski(k1_relat_1(sK0),X0) != iProver_top
% 2.01/0.97      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_992,c_611]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_8,plain,
% 2.01/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/0.97      | ~ v1_xboole_0(X2)
% 2.01/0.97      | v1_xboole_0(X0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_614,plain,
% 2.01/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.01/0.97      | v1_xboole_0(X2) != iProver_top
% 2.01/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1554,plain,
% 2.01/0.97      ( r1_tarski(k1_relat_1(sK0),X0) != iProver_top
% 2.01/0.97      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 2.01/0.97      | v1_xboole_0(X1) != iProver_top
% 2.01/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_1056,c_614]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_55,plain,
% 2.01/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_0,plain,
% 2.01/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 2.01/0.97      inference(cnf_transformation,[],[f29]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_64,plain,
% 2.01/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_390,plain,
% 2.01/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.01/0.97      theory(equality) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_737,plain,
% 2.01/0.97      ( ~ r1_tarski(X0,X1)
% 2.01/0.97      | r1_tarski(k2_relat_1(sK0),X1)
% 2.01/0.97      | k2_relat_1(sK0) != X0 ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_390]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_739,plain,
% 2.01/0.97      ( r1_tarski(k2_relat_1(sK0),k1_xboole_0)
% 2.01/0.97      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.01/0.97      | k2_relat_1(sK0) != k1_xboole_0 ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_737]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_745,plain,
% 2.01/0.97      ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
% 2.01/0.97      | k2_relat_1(sK0) = k1_xboole_0 ),
% 2.01/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_743]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_388,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_735,plain,
% 2.01/0.97      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_388]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_763,plain,
% 2.01/0.97      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_735]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_387,plain,( X0 = X0 ),theory(equality) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_764,plain,
% 2.01/0.97      ( sK0 = sK0 ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_387]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_772,plain,
% 2.01/0.97      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1,plain,
% 2.01/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.01/0.97      inference(cnf_transformation,[],[f30]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_824,plain,
% 2.01/0.97      ( ~ v1_xboole_0(sK0) | k1_xboole_0 = sK0 ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_929,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),X0)))
% 2.01/0.97      | ~ r1_tarski(k2_relat_1(sK0),X0)
% 2.01/0.97      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_209]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_931,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
% 2.01/0.97      | ~ r1_tarski(k2_relat_1(sK0),k1_xboole_0)
% 2.01/0.97      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_929]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_389,plain,
% 2.01/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.01/0.97      theory(equality) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_968,plain,
% 2.01/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_389]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_969,plain,
% 2.01/0.97      ( sK0 != X0
% 2.01/0.97      | v1_xboole_0(X0) != iProver_top
% 2.01/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_968]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_971,plain,
% 2.01/0.97      ( sK0 != k1_xboole_0
% 2.01/0.97      | v1_xboole_0(sK0) = iProver_top
% 2.01/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_969]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_963,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.01/0.97      | ~ v1_xboole_0(X1)
% 2.01/0.97      | v1_xboole_0(sK0) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1349,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),X0)))
% 2.01/0.97      | ~ v1_xboole_0(X0)
% 2.01/0.97      | v1_xboole_0(sK0) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_963]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1351,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
% 2.01/0.97      | v1_xboole_0(sK0)
% 2.01/0.97      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_1349]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1621,plain,
% 2.01/0.97      ( v1_xboole_0(sK0) = iProver_top ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_1554,c_55,c_0,c_64,c_739,c_745,c_763,c_764,c_772,
% 2.01/0.97                 c_824,c_931,c_971,c_1351]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_617,plain,
% 2.01/0.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1626,plain,
% 2.01/0.97      ( sK0 = k1_xboole_0 ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_1621,c_617]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_612,plain,
% 2.01/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.01/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1247,plain,
% 2.01/0.97      ( k1_relset_1(X0,X1,sK0) = k1_relat_1(sK0)
% 2.01/0.97      | r1_tarski(k1_relat_1(sK0),X0) != iProver_top
% 2.01/0.97      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_1056,c_612]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1630,plain,
% 2.01/0.97      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)
% 2.01/0.97      | r1_tarski(k1_relat_1(k1_xboole_0),X0) != iProver_top
% 2.01/0.97      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_1626,c_1247]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_5,plain,
% 2.01/0.97      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.01/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_860,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.01/0.97      | r1_tarski(k2_relat_1(sK0),k1_xboole_0) != iProver_top
% 2.01/0.97      | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_5,c_611]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_54,plain,
% 2.01/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_56,plain,
% 2.01/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_54]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_738,plain,
% 2.01/0.97      ( k2_relat_1(sK0) != X0
% 2.01/0.97      | r1_tarski(X0,X1) != iProver_top
% 2.01/0.97      | r1_tarski(k2_relat_1(sK0),X1) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_740,plain,
% 2.01/0.97      ( k2_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | r1_tarski(k2_relat_1(sK0),k1_xboole_0) = iProver_top
% 2.01/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_738]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_865,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.01/0.97      | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_860,c_56,c_740,c_745,c_772]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_991,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.01/0.97      inference(superposition,[status(thm)],[c_615,c_865]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1632,plain,
% 2.01/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_1626,c_991]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_12,plain,
% 2.01/0.97      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.01/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.01/0.97      | k1_xboole_0 = X0 ),
% 2.01/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_235,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.01/0.97      | k2_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) != X0
% 2.01/0.97      | sK0 != k1_xboole_0
% 2.01/0.97      | k1_xboole_0 = X0 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_105]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_236,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
% 2.01/0.97      | k2_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | sK0 != k1_xboole_0
% 2.01/0.97      | k1_xboole_0 = k1_relat_1(sK0) ),
% 2.01/0.97      inference(unflattening,[status(thm)],[c_235]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_610,plain,
% 2.01/0.97      ( k2_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | sK0 != k1_xboole_0
% 2.01/0.97      | k1_xboole_0 = k1_relat_1(sK0)
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.01/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_676,plain,
% 2.01/0.97      ( k2_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) = k1_xboole_0
% 2.01/0.97      | sK0 != k1_xboole_0
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.01/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_610,c_5]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_721,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0))))
% 2.01/0.97      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
% 2.01/0.97      | ~ r1_tarski(k1_relat_1(sK0),X0) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_209]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_771,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
% 2.01/0.97      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_721]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_773,plain,
% 2.01/0.97      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) = iProver_top
% 2.01/0.97      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
% 2.01/0.97      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_775,plain,
% 2.01/0.97      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_781,plain,
% 2.01/0.97      ( sK0 != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) = k1_xboole_0
% 2.01/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_676,c_727,c_745,c_773,c_772,c_775]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_782,plain,
% 2.01/0.97      ( k1_relat_1(sK0) = k1_xboole_0
% 2.01/0.97      | sK0 != k1_xboole_0
% 2.01/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.01/0.97      inference(renaming,[status(thm)],[c_781]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1635,plain,
% 2.01/0.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 2.01/0.97      | k1_xboole_0 != k1_xboole_0
% 2.01/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_1626,c_782]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1636,plain,
% 2.01/0.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 2.01/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.01/0.97      inference(equality_resolution_simp,[status(thm)],[c_1635]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1651,plain,
% 2.01/0.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.01/0.97      inference(backward_subsumption_resolution,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_1632,c_1636]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1665,plain,
% 2.01/0.97      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0
% 2.01/0.97      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 2.01/0.97      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.01/0.97      inference(light_normalisation,[status(thm)],[c_1630,c_1651]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1682,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 2.01/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.01/0.97      inference(instantiation,[status(thm)],[c_1665]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_14,plain,
% 2.01/0.97      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.01/0.97      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.01/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_262,plain,
% 2.01/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.01/0.97      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.01/0.97      | k2_relat_1(sK0) != X1
% 2.01/0.97      | k1_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | sK0 != X0 ),
% 2.01/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_105]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_263,plain,
% 2.01/0.97      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.01/0.97      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
% 2.01/0.97      | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) != k1_xboole_0 ),
% 2.01/0.97      inference(unflattening,[status(thm)],[c_262]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_609,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
% 2.01/0.97      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_6,plain,
% 2.01/0.97      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.01/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_667,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_609,c_6]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1054,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_992,c_667]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1067,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_1054,c_5]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1178,plain,
% 2.01/0.97      ( k1_relat_1(sK0) != k1_xboole_0
% 2.01/0.97      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0 ),
% 2.01/0.97      inference(global_propositional_subsumption,
% 2.01/0.97                [status(thm)],
% 2.01/0.97                [c_1067,c_991]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1179,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(sK0) != k1_xboole_0 ),
% 2.01/0.97      inference(renaming,[status(thm)],[c_1178]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1631,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.01/0.97      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 2.01/0.97      inference(demodulation,[status(thm)],[c_1626,c_1179]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1661,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.01/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 2.01/0.97      inference(light_normalisation,[status(thm)],[c_1631,c_1651]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(c_1662,plain,
% 2.01/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.01/0.97      inference(equality_resolution_simp,[status(thm)],[c_1661]) ).
% 2.01/0.97  
% 2.01/0.97  cnf(contradiction,plain,
% 2.01/0.97      ( $false ),
% 2.01/0.97      inference(minisat,[status(thm)],[c_1682,c_1662,c_56]) ).
% 2.01/0.97  
% 2.01/0.97  
% 2.01/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.01/0.97  
% 2.01/0.97  ------                               Statistics
% 2.01/0.97  
% 2.01/0.97  ------ General
% 2.01/0.97  
% 2.01/0.97  abstr_ref_over_cycles:                  0
% 2.01/0.97  abstr_ref_under_cycles:                 0
% 2.01/0.97  gc_basic_clause_elim:                   0
% 2.01/0.97  forced_gc_time:                         0
% 2.01/0.97  parsing_time:                           0.01
% 2.01/0.97  unif_index_cands_time:                  0.
% 2.01/0.97  unif_index_add_time:                    0.
% 2.01/0.97  orderings_time:                         0.
% 2.01/0.97  out_proof_time:                         0.009
% 2.01/0.97  total_time:                             0.082
% 2.01/0.97  num_of_symbols:                         44
% 2.01/0.97  num_of_terms:                           1366
% 2.01/0.97  
% 2.01/0.97  ------ Preprocessing
% 2.01/0.97  
% 2.01/0.97  num_of_splits:                          0
% 2.01/0.97  num_of_split_atoms:                     0
% 2.01/0.97  num_of_reused_defs:                     0
% 2.01/0.97  num_eq_ax_congr_red:                    5
% 2.01/0.97  num_of_sem_filtered_clauses:            2
% 2.01/0.97  num_of_subtypes:                        0
% 2.01/0.97  monotx_restored_types:                  0
% 2.01/0.97  sat_num_of_epr_types:                   0
% 2.01/0.97  sat_num_of_non_cyclic_types:            0
% 2.01/0.97  sat_guarded_non_collapsed_types:        0
% 2.01/0.97  num_pure_diseq_elim:                    0
% 2.01/0.97  simp_replaced_by:                       0
% 2.01/0.97  res_preprocessed:                       83
% 2.01/0.97  prep_upred:                             0
% 2.01/0.97  prep_unflattend:                        27
% 2.01/0.97  smt_new_axioms:                         0
% 2.01/0.97  pred_elim_cands:                        3
% 2.01/0.97  pred_elim:                              2
% 2.01/0.97  pred_elim_cl:                           5
% 2.01/0.97  pred_elim_cycles:                       4
% 2.01/0.97  merged_defs:                            0
% 2.01/0.97  merged_defs_ncl:                        0
% 2.01/0.97  bin_hyper_res:                          0
% 2.01/0.97  prep_cycles:                            4
% 2.01/0.97  pred_elim_time:                         0.003
% 2.01/0.97  splitting_time:                         0.
% 2.01/0.97  sem_filter_time:                        0.
% 2.01/0.97  monotx_time:                            0.
% 2.01/0.97  subtype_inf_time:                       0.
% 2.01/0.97  
% 2.01/0.97  ------ Problem properties
% 2.01/0.97  
% 2.01/0.97  clauses:                                14
% 2.01/0.97  conjectures:                            0
% 2.01/0.97  epr:                                    4
% 2.01/0.97  horn:                                   13
% 2.01/0.97  ground:                                 4
% 2.01/0.97  unary:                                  4
% 2.01/0.97  binary:                                 4
% 2.01/0.97  lits:                                   33
% 2.01/0.97  lits_eq:                                14
% 2.01/0.97  fd_pure:                                0
% 2.01/0.97  fd_pseudo:                              0
% 2.01/0.97  fd_cond:                                2
% 2.01/0.97  fd_pseudo_cond:                         1
% 2.01/0.97  ac_symbols:                             0
% 2.01/0.97  
% 2.01/0.97  ------ Propositional Solver
% 2.01/0.97  
% 2.01/0.97  prop_solver_calls:                      27
% 2.01/0.97  prop_fast_solver_calls:                 494
% 2.01/0.97  smt_solver_calls:                       0
% 2.01/0.97  smt_fast_solver_calls:                  0
% 2.01/0.97  prop_num_of_clauses:                    531
% 2.01/0.97  prop_preprocess_simplified:             2556
% 2.01/0.97  prop_fo_subsumed:                       9
% 2.01/0.97  prop_solver_time:                       0.
% 2.01/0.97  smt_solver_time:                        0.
% 2.01/0.97  smt_fast_solver_time:                   0.
% 2.01/0.97  prop_fast_solver_time:                  0.
% 2.01/0.97  prop_unsat_core_time:                   0.
% 2.01/0.97  
% 2.01/0.97  ------ QBF
% 2.01/0.97  
% 2.01/0.97  qbf_q_res:                              0
% 2.01/0.97  qbf_num_tautologies:                    0
% 2.01/0.97  qbf_prep_cycles:                        0
% 2.01/0.97  
% 2.01/0.97  ------ BMC1
% 2.01/0.97  
% 2.01/0.97  bmc1_current_bound:                     -1
% 2.01/0.97  bmc1_last_solved_bound:                 -1
% 2.01/0.97  bmc1_unsat_core_size:                   -1
% 2.01/0.97  bmc1_unsat_core_parents_size:           -1
% 2.01/0.97  bmc1_merge_next_fun:                    0
% 2.01/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.01/0.97  
% 2.01/0.97  ------ Instantiation
% 2.01/0.97  
% 2.01/0.97  inst_num_of_clauses:                    179
% 2.01/0.97  inst_num_in_passive:                    54
% 2.01/0.97  inst_num_in_active:                     107
% 2.01/0.97  inst_num_in_unprocessed:                18
% 2.01/0.98  inst_num_of_loops:                      130
% 2.01/0.98  inst_num_of_learning_restarts:          0
% 2.01/0.98  inst_num_moves_active_passive:          20
% 2.01/0.98  inst_lit_activity:                      0
% 2.01/0.98  inst_lit_activity_moves:                0
% 2.01/0.98  inst_num_tautologies:                   0
% 2.01/0.98  inst_num_prop_implied:                  0
% 2.01/0.98  inst_num_existing_simplified:           0
% 2.01/0.98  inst_num_eq_res_simplified:             0
% 2.01/0.98  inst_num_child_elim:                    0
% 2.01/0.98  inst_num_of_dismatching_blockings:      9
% 2.01/0.98  inst_num_of_non_proper_insts:           186
% 2.01/0.98  inst_num_of_duplicates:                 0
% 2.01/0.98  inst_inst_num_from_inst_to_res:         0
% 2.01/0.98  inst_dismatching_checking_time:         0.
% 2.01/0.98  
% 2.01/0.98  ------ Resolution
% 2.01/0.98  
% 2.01/0.98  res_num_of_clauses:                     0
% 2.01/0.98  res_num_in_passive:                     0
% 2.01/0.98  res_num_in_active:                      0
% 2.01/0.98  res_num_of_loops:                       87
% 2.01/0.98  res_forward_subset_subsumed:            18
% 2.01/0.98  res_backward_subset_subsumed:           0
% 2.01/0.98  res_forward_subsumed:                   0
% 2.01/0.98  res_backward_subsumed:                  0
% 2.01/0.98  res_forward_subsumption_resolution:     1
% 2.01/0.98  res_backward_subsumption_resolution:    0
% 2.01/0.98  res_clause_to_clause_subsumption:       72
% 2.01/0.98  res_orphan_elimination:                 0
% 2.01/0.98  res_tautology_del:                      40
% 2.01/0.98  res_num_eq_res_simplified:              0
% 2.01/0.98  res_num_sel_changes:                    0
% 2.01/0.98  res_moves_from_active_to_pass:          0
% 2.01/0.98  
% 2.01/0.98  ------ Superposition
% 2.01/0.98  
% 2.01/0.98  sup_time_total:                         0.
% 2.01/0.98  sup_time_generating:                    0.
% 2.01/0.98  sup_time_sim_full:                      0.
% 2.01/0.98  sup_time_sim_immed:                     0.
% 2.01/0.98  
% 2.01/0.98  sup_num_of_clauses:                     30
% 2.01/0.98  sup_num_in_active:                      12
% 2.01/0.98  sup_num_in_passive:                     18
% 2.01/0.98  sup_num_of_loops:                       25
% 2.01/0.98  sup_fw_superposition:                   20
% 2.01/0.98  sup_bw_superposition:                   6
% 2.01/0.98  sup_immediate_simplified:               12
% 2.01/0.98  sup_given_eliminated:                   0
% 2.01/0.98  comparisons_done:                       0
% 2.01/0.98  comparisons_avoided:                    0
% 2.01/0.98  
% 2.01/0.98  ------ Simplifications
% 2.01/0.98  
% 2.01/0.98  
% 2.01/0.98  sim_fw_subset_subsumed:                 2
% 2.01/0.98  sim_bw_subset_subsumed:                 2
% 2.01/0.98  sim_fw_subsumed:                        2
% 2.01/0.98  sim_bw_subsumed:                        0
% 2.01/0.98  sim_fw_subsumption_res:                 0
% 2.01/0.98  sim_bw_subsumption_res:                 1
% 2.01/0.98  sim_tautology_del:                      0
% 2.01/0.98  sim_eq_tautology_del:                   3
% 2.01/0.98  sim_eq_res_simp:                        2
% 2.01/0.98  sim_fw_demodulated:                     5
% 2.01/0.98  sim_bw_demodulated:                     12
% 2.01/0.98  sim_light_normalised:                   3
% 2.01/0.98  sim_joinable_taut:                      0
% 2.01/0.98  sim_joinable_simp:                      0
% 2.01/0.98  sim_ac_normalised:                      0
% 2.01/0.98  sim_smt_subsumption:                    0
% 2.01/0.98  
%------------------------------------------------------------------------------
