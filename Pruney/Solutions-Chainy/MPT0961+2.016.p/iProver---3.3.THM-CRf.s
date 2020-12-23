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
% DateTime   : Thu Dec  3 11:59:57 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  136 (1312 expanded)
%              Number of clauses        :   84 ( 484 expanded)
%              Number of leaves         :   11 ( 221 expanded)
%              Depth                    :   23
%              Number of atoms          :  426 (5011 expanded)
%              Number of equality atoms :  203 (1297 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f29,plain,
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

fof(f30,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f29])).

fof(f55,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f50])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_118,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_23])).

cnf(c_119,negated_conjecture,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(renaming,[status(thm)],[c_118])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK0) != X1
    | k2_relat_1(sK0) != X2
    | sK0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_119])).

cnf(c_341,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_349,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_341,c_14])).

cnf(c_890,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_2070,plain,
    ( k2_relat_1(sK0) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_890])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_131,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_9,c_7])).

cnf(c_132,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_131])).

cnf(c_1041,plain,
    ( ~ r1_tarski(X0,sK0)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_1118,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1119,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1056,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k1_relat_1(sK0),X0)
    | ~ r1_tarski(k2_relat_1(sK0),X1)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1138,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),X0)))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(sK0),X0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1223,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_1224,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_900,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1410,plain,
    ( k2_relat_1(sK0) = k1_xboole_0
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_890])).

cnf(c_1415,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | k2_relat_1(sK0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1410])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1241,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0))
    | r1_tarski(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1639,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1241])).

cnf(c_2121,plain,
    ( k2_relat_1(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2070,c_24,c_1118,c_1119,c_1223,c_1224,c_1415,c_1639])).

cnf(c_902,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2066,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_897])).

cnf(c_2923,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_2066])).

cnf(c_5545,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2121,c_2923])).

cnf(c_25,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_67,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_69,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_5822,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5545,c_25,c_69])).

cnf(c_16,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_297,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_relat_1(sK0) != X0
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_119])).

cnf(c_298,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_892,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK0)
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_981,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_892,c_4])).

cnf(c_62,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_64,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_1067,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | sK0 != k1_xboole_0
    | k2_relat_1(sK0) != k1_xboole_0
    | k1_relat_1(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_981,c_64,c_69])).

cnf(c_1068,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | k2_relat_1(sK0) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1067])).

cnf(c_2124,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2121,c_1068])).

cnf(c_2135,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2124])).

cnf(c_2139,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2135,c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1080,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1081,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1080])).

cnf(c_1097,plain,
    ( r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1100,plain,
    ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_1120,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

cnf(c_1122,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_1151,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1152,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_1225,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) = iProver_top
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1223])).

cnf(c_1227,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1224])).

cnf(c_2476,plain,
    ( k1_relat_1(sK0) = k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2139,c_24,c_25,c_1068,c_1081,c_1100,c_1118,c_1120,c_1119,c_1122,c_1152,c_1223,c_1225,c_1224,c_1227,c_1415,c_1639])).

cnf(c_5828,plain,
    ( k1_relat_1(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5822,c_2476])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_898,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1587,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_898])).

cnf(c_5829,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK0) = k1_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_5822,c_1587])).

cnf(c_5836,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5828,c_5829])).

cnf(c_5846,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5836])).

cnf(c_18,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | k2_relat_1(sK0) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_119])).

cnf(c_325,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
    | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_891,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_972,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_891,c_5])).

cnf(c_2125,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2121,c_972])).

cnf(c_2131,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | k1_relat_1(sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2125,c_4])).

cnf(c_2358,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2131,c_24,c_25,c_1068,c_1081,c_1100,c_1118,c_1120,c_1119,c_1122,c_1152,c_1223,c_1225,c_1224,c_1227,c_1415,c_1639])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5846,c_5545,c_2358,c_69,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.44/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/0.99  
% 2.44/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/0.99  
% 2.44/0.99  ------  iProver source info
% 2.44/0.99  
% 2.44/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.44/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/0.99  git: non_committed_changes: false
% 2.44/0.99  git: last_make_outside_of_git: false
% 2.44/0.99  
% 2.44/0.99  ------ 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options
% 2.44/0.99  
% 2.44/0.99  --out_options                           all
% 2.44/0.99  --tptp_safe_out                         true
% 2.44/0.99  --problem_path                          ""
% 2.44/0.99  --include_path                          ""
% 2.44/0.99  --clausifier                            res/vclausify_rel
% 2.44/0.99  --clausifier_options                    --mode clausify
% 2.44/0.99  --stdin                                 false
% 2.44/0.99  --stats_out                             all
% 2.44/0.99  
% 2.44/0.99  ------ General Options
% 2.44/0.99  
% 2.44/0.99  --fof                                   false
% 2.44/0.99  --time_out_real                         305.
% 2.44/0.99  --time_out_virtual                      -1.
% 2.44/0.99  --symbol_type_check                     false
% 2.44/0.99  --clausify_out                          false
% 2.44/0.99  --sig_cnt_out                           false
% 2.44/0.99  --trig_cnt_out                          false
% 2.44/0.99  --trig_cnt_out_tolerance                1.
% 2.44/0.99  --trig_cnt_out_sk_spl                   false
% 2.44/0.99  --abstr_cl_out                          false
% 2.44/0.99  
% 2.44/0.99  ------ Global Options
% 2.44/0.99  
% 2.44/0.99  --schedule                              default
% 2.44/0.99  --add_important_lit                     false
% 2.44/0.99  --prop_solver_per_cl                    1000
% 2.44/0.99  --min_unsat_core                        false
% 2.44/0.99  --soft_assumptions                      false
% 2.44/0.99  --soft_lemma_size                       3
% 2.44/0.99  --prop_impl_unit_size                   0
% 2.44/0.99  --prop_impl_unit                        []
% 2.44/0.99  --share_sel_clauses                     true
% 2.44/0.99  --reset_solvers                         false
% 2.44/0.99  --bc_imp_inh                            [conj_cone]
% 2.44/0.99  --conj_cone_tolerance                   3.
% 2.44/0.99  --extra_neg_conj                        none
% 2.44/0.99  --large_theory_mode                     true
% 2.44/0.99  --prolific_symb_bound                   200
% 2.44/0.99  --lt_threshold                          2000
% 2.44/0.99  --clause_weak_htbl                      true
% 2.44/0.99  --gc_record_bc_elim                     false
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing Options
% 2.44/0.99  
% 2.44/0.99  --preprocessing_flag                    true
% 2.44/0.99  --time_out_prep_mult                    0.1
% 2.44/0.99  --splitting_mode                        input
% 2.44/0.99  --splitting_grd                         true
% 2.44/0.99  --splitting_cvd                         false
% 2.44/0.99  --splitting_cvd_svl                     false
% 2.44/0.99  --splitting_nvd                         32
% 2.44/0.99  --sub_typing                            true
% 2.44/0.99  --prep_gs_sim                           true
% 2.44/0.99  --prep_unflatten                        true
% 2.44/0.99  --prep_res_sim                          true
% 2.44/0.99  --prep_upred                            true
% 2.44/0.99  --prep_sem_filter                       exhaustive
% 2.44/0.99  --prep_sem_filter_out                   false
% 2.44/0.99  --pred_elim                             true
% 2.44/0.99  --res_sim_input                         true
% 2.44/0.99  --eq_ax_congr_red                       true
% 2.44/0.99  --pure_diseq_elim                       true
% 2.44/0.99  --brand_transform                       false
% 2.44/0.99  --non_eq_to_eq                          false
% 2.44/0.99  --prep_def_merge                        true
% 2.44/0.99  --prep_def_merge_prop_impl              false
% 2.44/0.99  --prep_def_merge_mbd                    true
% 2.44/0.99  --prep_def_merge_tr_red                 false
% 2.44/0.99  --prep_def_merge_tr_cl                  false
% 2.44/0.99  --smt_preprocessing                     true
% 2.44/0.99  --smt_ac_axioms                         fast
% 2.44/0.99  --preprocessed_out                      false
% 2.44/0.99  --preprocessed_stats                    false
% 2.44/0.99  
% 2.44/0.99  ------ Abstraction refinement Options
% 2.44/0.99  
% 2.44/0.99  --abstr_ref                             []
% 2.44/0.99  --abstr_ref_prep                        false
% 2.44/0.99  --abstr_ref_until_sat                   false
% 2.44/0.99  --abstr_ref_sig_restrict                funpre
% 2.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.99  --abstr_ref_under                       []
% 2.44/0.99  
% 2.44/0.99  ------ SAT Options
% 2.44/0.99  
% 2.44/0.99  --sat_mode                              false
% 2.44/0.99  --sat_fm_restart_options                ""
% 2.44/0.99  --sat_gr_def                            false
% 2.44/0.99  --sat_epr_types                         true
% 2.44/0.99  --sat_non_cyclic_types                  false
% 2.44/0.99  --sat_finite_models                     false
% 2.44/0.99  --sat_fm_lemmas                         false
% 2.44/0.99  --sat_fm_prep                           false
% 2.44/0.99  --sat_fm_uc_incr                        true
% 2.44/0.99  --sat_out_model                         small
% 2.44/0.99  --sat_out_clauses                       false
% 2.44/0.99  
% 2.44/0.99  ------ QBF Options
% 2.44/0.99  
% 2.44/0.99  --qbf_mode                              false
% 2.44/0.99  --qbf_elim_univ                         false
% 2.44/0.99  --qbf_dom_inst                          none
% 2.44/0.99  --qbf_dom_pre_inst                      false
% 2.44/0.99  --qbf_sk_in                             false
% 2.44/0.99  --qbf_pred_elim                         true
% 2.44/0.99  --qbf_split                             512
% 2.44/0.99  
% 2.44/0.99  ------ BMC1 Options
% 2.44/0.99  
% 2.44/0.99  --bmc1_incremental                      false
% 2.44/0.99  --bmc1_axioms                           reachable_all
% 2.44/0.99  --bmc1_min_bound                        0
% 2.44/0.99  --bmc1_max_bound                        -1
% 2.44/0.99  --bmc1_max_bound_default                -1
% 2.44/0.99  --bmc1_symbol_reachability              true
% 2.44/0.99  --bmc1_property_lemmas                  false
% 2.44/0.99  --bmc1_k_induction                      false
% 2.44/0.99  --bmc1_non_equiv_states                 false
% 2.44/0.99  --bmc1_deadlock                         false
% 2.44/0.99  --bmc1_ucm                              false
% 2.44/0.99  --bmc1_add_unsat_core                   none
% 2.44/0.99  --bmc1_unsat_core_children              false
% 2.44/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.99  --bmc1_out_stat                         full
% 2.44/0.99  --bmc1_ground_init                      false
% 2.44/0.99  --bmc1_pre_inst_next_state              false
% 2.44/0.99  --bmc1_pre_inst_state                   false
% 2.44/0.99  --bmc1_pre_inst_reach_state             false
% 2.44/0.99  --bmc1_out_unsat_core                   false
% 2.44/0.99  --bmc1_aig_witness_out                  false
% 2.44/0.99  --bmc1_verbose                          false
% 2.44/0.99  --bmc1_dump_clauses_tptp                false
% 2.44/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.99  --bmc1_dump_file                        -
% 2.44/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.99  --bmc1_ucm_extend_mode                  1
% 2.44/0.99  --bmc1_ucm_init_mode                    2
% 2.44/0.99  --bmc1_ucm_cone_mode                    none
% 2.44/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.99  --bmc1_ucm_relax_model                  4
% 2.44/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.99  --bmc1_ucm_layered_model                none
% 2.44/0.99  --bmc1_ucm_max_lemma_size               10
% 2.44/0.99  
% 2.44/0.99  ------ AIG Options
% 2.44/0.99  
% 2.44/0.99  --aig_mode                              false
% 2.44/0.99  
% 2.44/0.99  ------ Instantiation Options
% 2.44/0.99  
% 2.44/0.99  --instantiation_flag                    true
% 2.44/0.99  --inst_sos_flag                         false
% 2.44/0.99  --inst_sos_phase                        true
% 2.44/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel_side                     num_symb
% 2.44/0.99  --inst_solver_per_active                1400
% 2.44/0.99  --inst_solver_calls_frac                1.
% 2.44/0.99  --inst_passive_queue_type               priority_queues
% 2.44/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.99  --inst_passive_queues_freq              [25;2]
% 2.44/0.99  --inst_dismatching                      true
% 2.44/0.99  --inst_eager_unprocessed_to_passive     true
% 2.44/0.99  --inst_prop_sim_given                   true
% 2.44/0.99  --inst_prop_sim_new                     false
% 2.44/0.99  --inst_subs_new                         false
% 2.44/0.99  --inst_eq_res_simp                      false
% 2.44/0.99  --inst_subs_given                       false
% 2.44/0.99  --inst_orphan_elimination               true
% 2.44/0.99  --inst_learning_loop_flag               true
% 2.44/0.99  --inst_learning_start                   3000
% 2.44/0.99  --inst_learning_factor                  2
% 2.44/0.99  --inst_start_prop_sim_after_learn       3
% 2.44/0.99  --inst_sel_renew                        solver
% 2.44/0.99  --inst_lit_activity_flag                true
% 2.44/0.99  --inst_restr_to_given                   false
% 2.44/0.99  --inst_activity_threshold               500
% 2.44/0.99  --inst_out_proof                        true
% 2.44/0.99  
% 2.44/0.99  ------ Resolution Options
% 2.44/0.99  
% 2.44/0.99  --resolution_flag                       true
% 2.44/0.99  --res_lit_sel                           adaptive
% 2.44/0.99  --res_lit_sel_side                      none
% 2.44/0.99  --res_ordering                          kbo
% 2.44/0.99  --res_to_prop_solver                    active
% 2.44/0.99  --res_prop_simpl_new                    false
% 2.44/0.99  --res_prop_simpl_given                  true
% 2.44/0.99  --res_passive_queue_type                priority_queues
% 2.44/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.99  --res_passive_queues_freq               [15;5]
% 2.44/0.99  --res_forward_subs                      full
% 2.44/0.99  --res_backward_subs                     full
% 2.44/0.99  --res_forward_subs_resolution           true
% 2.44/0.99  --res_backward_subs_resolution          true
% 2.44/0.99  --res_orphan_elimination                true
% 2.44/0.99  --res_time_limit                        2.
% 2.44/0.99  --res_out_proof                         true
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Options
% 2.44/0.99  
% 2.44/0.99  --superposition_flag                    true
% 2.44/0.99  --sup_passive_queue_type                priority_queues
% 2.44/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.99  --demod_completeness_check              fast
% 2.44/0.99  --demod_use_ground                      true
% 2.44/0.99  --sup_to_prop_solver                    passive
% 2.44/0.99  --sup_prop_simpl_new                    true
% 2.44/0.99  --sup_prop_simpl_given                  true
% 2.44/0.99  --sup_fun_splitting                     false
% 2.44/0.99  --sup_smt_interval                      50000
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Simplification Setup
% 2.44/0.99  
% 2.44/0.99  --sup_indices_passive                   []
% 2.44/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_full_bw                           [BwDemod]
% 2.44/0.99  --sup_immed_triv                        [TrivRules]
% 2.44/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_immed_bw_main                     []
% 2.44/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  
% 2.44/0.99  ------ Combination Options
% 2.44/0.99  
% 2.44/0.99  --comb_res_mult                         3
% 2.44/0.99  --comb_sup_mult                         2
% 2.44/0.99  --comb_inst_mult                        10
% 2.44/0.99  
% 2.44/0.99  ------ Debug Options
% 2.44/0.99  
% 2.44/0.99  --dbg_backtrace                         false
% 2.44/0.99  --dbg_dump_prop_clauses                 false
% 2.44/0.99  --dbg_dump_prop_clauses_file            -
% 2.44/0.99  --dbg_out_stat                          false
% 2.44/0.99  ------ Parsing...
% 2.44/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/0.99  ------ Proving...
% 2.44/0.99  ------ Problem Properties 
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  clauses                                 19
% 2.44/0.99  conjectures                             1
% 2.44/0.99  EPR                                     5
% 2.44/0.99  Horn                                    18
% 2.44/0.99  unary                                   7
% 2.44/0.99  binary                                  4
% 2.44/0.99  lits                                    43
% 2.44/0.99  lits eq                                 15
% 2.44/0.99  fd_pure                                 0
% 2.44/0.99  fd_pseudo                               0
% 2.44/0.99  fd_cond                                 1
% 2.44/0.99  fd_pseudo_cond                          1
% 2.44/0.99  AC symbols                              0
% 2.44/0.99  
% 2.44/0.99  ------ Schedule dynamic 5 is on 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  ------ 
% 2.44/0.99  Current options:
% 2.44/0.99  ------ 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options
% 2.44/0.99  
% 2.44/0.99  --out_options                           all
% 2.44/0.99  --tptp_safe_out                         true
% 2.44/0.99  --problem_path                          ""
% 2.44/0.99  --include_path                          ""
% 2.44/0.99  --clausifier                            res/vclausify_rel
% 2.44/0.99  --clausifier_options                    --mode clausify
% 2.44/0.99  --stdin                                 false
% 2.44/0.99  --stats_out                             all
% 2.44/0.99  
% 2.44/0.99  ------ General Options
% 2.44/0.99  
% 2.44/0.99  --fof                                   false
% 2.44/0.99  --time_out_real                         305.
% 2.44/0.99  --time_out_virtual                      -1.
% 2.44/0.99  --symbol_type_check                     false
% 2.44/0.99  --clausify_out                          false
% 2.44/0.99  --sig_cnt_out                           false
% 2.44/0.99  --trig_cnt_out                          false
% 2.44/0.99  --trig_cnt_out_tolerance                1.
% 2.44/0.99  --trig_cnt_out_sk_spl                   false
% 2.44/0.99  --abstr_cl_out                          false
% 2.44/0.99  
% 2.44/0.99  ------ Global Options
% 2.44/0.99  
% 2.44/0.99  --schedule                              default
% 2.44/0.99  --add_important_lit                     false
% 2.44/0.99  --prop_solver_per_cl                    1000
% 2.44/0.99  --min_unsat_core                        false
% 2.44/0.99  --soft_assumptions                      false
% 2.44/0.99  --soft_lemma_size                       3
% 2.44/0.99  --prop_impl_unit_size                   0
% 2.44/0.99  --prop_impl_unit                        []
% 2.44/0.99  --share_sel_clauses                     true
% 2.44/0.99  --reset_solvers                         false
% 2.44/0.99  --bc_imp_inh                            [conj_cone]
% 2.44/0.99  --conj_cone_tolerance                   3.
% 2.44/0.99  --extra_neg_conj                        none
% 2.44/0.99  --large_theory_mode                     true
% 2.44/0.99  --prolific_symb_bound                   200
% 2.44/0.99  --lt_threshold                          2000
% 2.44/0.99  --clause_weak_htbl                      true
% 2.44/0.99  --gc_record_bc_elim                     false
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing Options
% 2.44/0.99  
% 2.44/0.99  --preprocessing_flag                    true
% 2.44/0.99  --time_out_prep_mult                    0.1
% 2.44/0.99  --splitting_mode                        input
% 2.44/0.99  --splitting_grd                         true
% 2.44/0.99  --splitting_cvd                         false
% 2.44/0.99  --splitting_cvd_svl                     false
% 2.44/0.99  --splitting_nvd                         32
% 2.44/0.99  --sub_typing                            true
% 2.44/0.99  --prep_gs_sim                           true
% 2.44/0.99  --prep_unflatten                        true
% 2.44/0.99  --prep_res_sim                          true
% 2.44/0.99  --prep_upred                            true
% 2.44/0.99  --prep_sem_filter                       exhaustive
% 2.44/0.99  --prep_sem_filter_out                   false
% 2.44/0.99  --pred_elim                             true
% 2.44/0.99  --res_sim_input                         true
% 2.44/0.99  --eq_ax_congr_red                       true
% 2.44/0.99  --pure_diseq_elim                       true
% 2.44/0.99  --brand_transform                       false
% 2.44/0.99  --non_eq_to_eq                          false
% 2.44/0.99  --prep_def_merge                        true
% 2.44/0.99  --prep_def_merge_prop_impl              false
% 2.44/0.99  --prep_def_merge_mbd                    true
% 2.44/0.99  --prep_def_merge_tr_red                 false
% 2.44/0.99  --prep_def_merge_tr_cl                  false
% 2.44/0.99  --smt_preprocessing                     true
% 2.44/0.99  --smt_ac_axioms                         fast
% 2.44/0.99  --preprocessed_out                      false
% 2.44/0.99  --preprocessed_stats                    false
% 2.44/0.99  
% 2.44/0.99  ------ Abstraction refinement Options
% 2.44/0.99  
% 2.44/0.99  --abstr_ref                             []
% 2.44/0.99  --abstr_ref_prep                        false
% 2.44/0.99  --abstr_ref_until_sat                   false
% 2.44/0.99  --abstr_ref_sig_restrict                funpre
% 2.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.99  --abstr_ref_under                       []
% 2.44/0.99  
% 2.44/0.99  ------ SAT Options
% 2.44/0.99  
% 2.44/0.99  --sat_mode                              false
% 2.44/0.99  --sat_fm_restart_options                ""
% 2.44/0.99  --sat_gr_def                            false
% 2.44/0.99  --sat_epr_types                         true
% 2.44/0.99  --sat_non_cyclic_types                  false
% 2.44/0.99  --sat_finite_models                     false
% 2.44/0.99  --sat_fm_lemmas                         false
% 2.44/0.99  --sat_fm_prep                           false
% 2.44/0.99  --sat_fm_uc_incr                        true
% 2.44/0.99  --sat_out_model                         small
% 2.44/0.99  --sat_out_clauses                       false
% 2.44/0.99  
% 2.44/0.99  ------ QBF Options
% 2.44/0.99  
% 2.44/0.99  --qbf_mode                              false
% 2.44/0.99  --qbf_elim_univ                         false
% 2.44/0.99  --qbf_dom_inst                          none
% 2.44/0.99  --qbf_dom_pre_inst                      false
% 2.44/0.99  --qbf_sk_in                             false
% 2.44/0.99  --qbf_pred_elim                         true
% 2.44/0.99  --qbf_split                             512
% 2.44/0.99  
% 2.44/0.99  ------ BMC1 Options
% 2.44/0.99  
% 2.44/0.99  --bmc1_incremental                      false
% 2.44/0.99  --bmc1_axioms                           reachable_all
% 2.44/0.99  --bmc1_min_bound                        0
% 2.44/0.99  --bmc1_max_bound                        -1
% 2.44/0.99  --bmc1_max_bound_default                -1
% 2.44/0.99  --bmc1_symbol_reachability              true
% 2.44/0.99  --bmc1_property_lemmas                  false
% 2.44/0.99  --bmc1_k_induction                      false
% 2.44/0.99  --bmc1_non_equiv_states                 false
% 2.44/0.99  --bmc1_deadlock                         false
% 2.44/0.99  --bmc1_ucm                              false
% 2.44/0.99  --bmc1_add_unsat_core                   none
% 2.44/0.99  --bmc1_unsat_core_children              false
% 2.44/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.99  --bmc1_out_stat                         full
% 2.44/0.99  --bmc1_ground_init                      false
% 2.44/0.99  --bmc1_pre_inst_next_state              false
% 2.44/0.99  --bmc1_pre_inst_state                   false
% 2.44/0.99  --bmc1_pre_inst_reach_state             false
% 2.44/0.99  --bmc1_out_unsat_core                   false
% 2.44/0.99  --bmc1_aig_witness_out                  false
% 2.44/0.99  --bmc1_verbose                          false
% 2.44/0.99  --bmc1_dump_clauses_tptp                false
% 2.44/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.99  --bmc1_dump_file                        -
% 2.44/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.99  --bmc1_ucm_extend_mode                  1
% 2.44/0.99  --bmc1_ucm_init_mode                    2
% 2.44/0.99  --bmc1_ucm_cone_mode                    none
% 2.44/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.99  --bmc1_ucm_relax_model                  4
% 2.44/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.99  --bmc1_ucm_layered_model                none
% 2.44/0.99  --bmc1_ucm_max_lemma_size               10
% 2.44/0.99  
% 2.44/0.99  ------ AIG Options
% 2.44/0.99  
% 2.44/0.99  --aig_mode                              false
% 2.44/0.99  
% 2.44/0.99  ------ Instantiation Options
% 2.44/0.99  
% 2.44/0.99  --instantiation_flag                    true
% 2.44/0.99  --inst_sos_flag                         false
% 2.44/0.99  --inst_sos_phase                        true
% 2.44/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel_side                     none
% 2.44/0.99  --inst_solver_per_active                1400
% 2.44/0.99  --inst_solver_calls_frac                1.
% 2.44/0.99  --inst_passive_queue_type               priority_queues
% 2.44/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.99  --inst_passive_queues_freq              [25;2]
% 2.44/0.99  --inst_dismatching                      true
% 2.44/0.99  --inst_eager_unprocessed_to_passive     true
% 2.44/0.99  --inst_prop_sim_given                   true
% 2.44/0.99  --inst_prop_sim_new                     false
% 2.44/0.99  --inst_subs_new                         false
% 2.44/0.99  --inst_eq_res_simp                      false
% 2.44/0.99  --inst_subs_given                       false
% 2.44/0.99  --inst_orphan_elimination               true
% 2.44/0.99  --inst_learning_loop_flag               true
% 2.44/0.99  --inst_learning_start                   3000
% 2.44/0.99  --inst_learning_factor                  2
% 2.44/0.99  --inst_start_prop_sim_after_learn       3
% 2.44/0.99  --inst_sel_renew                        solver
% 2.44/0.99  --inst_lit_activity_flag                true
% 2.44/0.99  --inst_restr_to_given                   false
% 2.44/0.99  --inst_activity_threshold               500
% 2.44/0.99  --inst_out_proof                        true
% 2.44/0.99  
% 2.44/0.99  ------ Resolution Options
% 2.44/0.99  
% 2.44/0.99  --resolution_flag                       false
% 2.44/0.99  --res_lit_sel                           adaptive
% 2.44/0.99  --res_lit_sel_side                      none
% 2.44/0.99  --res_ordering                          kbo
% 2.44/0.99  --res_to_prop_solver                    active
% 2.44/0.99  --res_prop_simpl_new                    false
% 2.44/0.99  --res_prop_simpl_given                  true
% 2.44/0.99  --res_passive_queue_type                priority_queues
% 2.44/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.99  --res_passive_queues_freq               [15;5]
% 2.44/0.99  --res_forward_subs                      full
% 2.44/0.99  --res_backward_subs                     full
% 2.44/0.99  --res_forward_subs_resolution           true
% 2.44/0.99  --res_backward_subs_resolution          true
% 2.44/0.99  --res_orphan_elimination                true
% 2.44/0.99  --res_time_limit                        2.
% 2.44/0.99  --res_out_proof                         true
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Options
% 2.44/0.99  
% 2.44/0.99  --superposition_flag                    true
% 2.44/0.99  --sup_passive_queue_type                priority_queues
% 2.44/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.99  --demod_completeness_check              fast
% 2.44/0.99  --demod_use_ground                      true
% 2.44/0.99  --sup_to_prop_solver                    passive
% 2.44/0.99  --sup_prop_simpl_new                    true
% 2.44/0.99  --sup_prop_simpl_given                  true
% 2.44/0.99  --sup_fun_splitting                     false
% 2.44/0.99  --sup_smt_interval                      50000
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Simplification Setup
% 2.44/0.99  
% 2.44/0.99  --sup_indices_passive                   []
% 2.44/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_full_bw                           [BwDemod]
% 2.44/0.99  --sup_immed_triv                        [TrivRules]
% 2.44/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_immed_bw_main                     []
% 2.44/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  
% 2.44/0.99  ------ Combination Options
% 2.44/0.99  
% 2.44/0.99  --comb_res_mult                         3
% 2.44/0.99  --comb_sup_mult                         2
% 2.44/0.99  --comb_inst_mult                        10
% 2.44/0.99  
% 2.44/0.99  ------ Debug Options
% 2.44/0.99  
% 2.44/0.99  --dbg_backtrace                         false
% 2.44/0.99  --dbg_dump_prop_clauses                 false
% 2.44/0.99  --dbg_dump_prop_clauses_file            -
% 2.44/0.99  --dbg_out_stat                          false
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  ------ Proving...
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  % SZS status Theorem for theBenchmark.p
% 2.44/0.99  
% 2.44/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/0.99  
% 2.44/0.99  fof(f9,axiom,(
% 2.44/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f17,plain,(
% 2.44/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.44/0.99    inference(ennf_transformation,[],[f9])).
% 2.44/0.99  
% 2.44/0.99  fof(f18,plain,(
% 2.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.44/0.99    inference(flattening,[],[f17])).
% 2.44/0.99  
% 2.44/0.99  fof(f46,plain,(
% 2.44/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f18])).
% 2.44/0.99  
% 2.44/0.99  fof(f10,axiom,(
% 2.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f19,plain,(
% 2.44/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/0.99    inference(ennf_transformation,[],[f10])).
% 2.44/0.99  
% 2.44/0.99  fof(f20,plain,(
% 2.44/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/0.99    inference(flattening,[],[f19])).
% 2.44/0.99  
% 2.44/0.99  fof(f28,plain,(
% 2.44/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/0.99    inference(nnf_transformation,[],[f20])).
% 2.44/0.99  
% 2.44/0.99  fof(f49,plain,(
% 2.44/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/0.99    inference(cnf_transformation,[],[f28])).
% 2.44/0.99  
% 2.44/0.99  fof(f11,conjecture,(
% 2.44/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f12,negated_conjecture,(
% 2.44/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.44/0.99    inference(negated_conjecture,[],[f11])).
% 2.44/0.99  
% 2.44/0.99  fof(f21,plain,(
% 2.44/0.99    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.44/0.99    inference(ennf_transformation,[],[f12])).
% 2.44/0.99  
% 2.44/0.99  fof(f22,plain,(
% 2.44/0.99    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.44/0.99    inference(flattening,[],[f21])).
% 2.44/0.99  
% 2.44/0.99  fof(f29,plain,(
% 2.44/0.99    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f30,plain,(
% 2.44/0.99    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f29])).
% 2.44/0.99  
% 2.44/0.99  fof(f55,plain,(
% 2.44/0.99    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 2.44/0.99    inference(cnf_transformation,[],[f30])).
% 2.44/0.99  
% 2.44/0.99  fof(f54,plain,(
% 2.44/0.99    v1_funct_1(sK0)),
% 2.44/0.99    inference(cnf_transformation,[],[f30])).
% 2.44/0.99  
% 2.44/0.99  fof(f8,axiom,(
% 2.44/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f16,plain,(
% 2.44/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.44/0.99    inference(ennf_transformation,[],[f8])).
% 2.44/0.99  
% 2.44/0.99  fof(f45,plain,(
% 2.44/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/0.99    inference(cnf_transformation,[],[f16])).
% 2.44/0.99  
% 2.44/0.99  fof(f53,plain,(
% 2.44/0.99    v1_relat_1(sK0)),
% 2.44/0.99    inference(cnf_transformation,[],[f30])).
% 2.44/0.99  
% 2.44/0.99  fof(f6,axiom,(
% 2.44/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f14,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.44/0.99    inference(ennf_transformation,[],[f6])).
% 2.44/0.99  
% 2.44/0.99  fof(f15,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.44/0.99    inference(flattening,[],[f14])).
% 2.44/0.99  
% 2.44/0.99  fof(f41,plain,(
% 2.44/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f15])).
% 2.44/0.99  
% 2.44/0.99  fof(f5,axiom,(
% 2.44/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f13,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.44/0.99    inference(ennf_transformation,[],[f5])).
% 2.44/0.99  
% 2.44/0.99  fof(f40,plain,(
% 2.44/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f13])).
% 2.44/0.99  
% 2.44/0.99  fof(f4,axiom,(
% 2.44/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f27,plain,(
% 2.44/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.44/0.99    inference(nnf_transformation,[],[f4])).
% 2.44/0.99  
% 2.44/0.99  fof(f39,plain,(
% 2.44/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f27])).
% 2.44/0.99  
% 2.44/0.99  fof(f1,axiom,(
% 2.44/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f23,plain,(
% 2.44/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.44/0.99    inference(nnf_transformation,[],[f1])).
% 2.44/0.99  
% 2.44/0.99  fof(f24,plain,(
% 2.44/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.44/0.99    inference(flattening,[],[f23])).
% 2.44/0.99  
% 2.44/0.99  fof(f31,plain,(
% 2.44/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.44/0.99    inference(cnf_transformation,[],[f24])).
% 2.44/0.99  
% 2.44/0.99  fof(f57,plain,(
% 2.44/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.44/0.99    inference(equality_resolution,[],[f31])).
% 2.44/0.99  
% 2.44/0.99  fof(f38,plain,(
% 2.44/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.44/0.99    inference(cnf_transformation,[],[f27])).
% 2.44/0.99  
% 2.44/0.99  fof(f3,axiom,(
% 2.44/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f25,plain,(
% 2.44/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.44/0.99    inference(nnf_transformation,[],[f3])).
% 2.44/0.99  
% 2.44/0.99  fof(f26,plain,(
% 2.44/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.44/0.99    inference(flattening,[],[f25])).
% 2.44/0.99  
% 2.44/0.99  fof(f37,plain,(
% 2.44/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.44/0.99    inference(cnf_transformation,[],[f26])).
% 2.44/0.99  
% 2.44/0.99  fof(f58,plain,(
% 2.44/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.44/0.99    inference(equality_resolution,[],[f37])).
% 2.44/0.99  
% 2.44/0.99  fof(f2,axiom,(
% 2.44/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f34,plain,(
% 2.44/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f2])).
% 2.44/0.99  
% 2.44/0.99  fof(f52,plain,(
% 2.44/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/0.99    inference(cnf_transformation,[],[f28])).
% 2.44/0.99  
% 2.44/0.99  fof(f60,plain,(
% 2.44/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/0.99    inference(equality_resolution,[],[f52])).
% 2.44/0.99  
% 2.44/0.99  fof(f61,plain,(
% 2.44/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.44/0.99    inference(equality_resolution,[],[f60])).
% 2.44/0.99  
% 2.44/0.99  fof(f33,plain,(
% 2.44/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f24])).
% 2.44/0.99  
% 2.44/0.99  fof(f36,plain,(
% 2.44/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.44/0.99    inference(cnf_transformation,[],[f26])).
% 2.44/0.99  
% 2.44/0.99  fof(f59,plain,(
% 2.44/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.44/0.99    inference(equality_resolution,[],[f36])).
% 2.44/0.99  
% 2.44/0.99  fof(f50,plain,(
% 2.44/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.44/0.99    inference(cnf_transformation,[],[f28])).
% 2.44/0.99  
% 2.44/0.99  fof(f63,plain,(
% 2.44/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.44/0.99    inference(equality_resolution,[],[f50])).
% 2.44/0.99  
% 2.44/0.99  cnf(c_15,plain,
% 2.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.44/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.44/0.99      | ~ v1_relat_1(X0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_897,plain,
% 2.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.44/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.44/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 2.44/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_19,plain,
% 2.44/0.99      ( v1_funct_2(X0,X1,X2)
% 2.44/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.44/0.99      | k1_xboole_0 = X2 ),
% 2.44/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_22,negated_conjecture,
% 2.44/0.99      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 2.44/0.99      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/0.99      | ~ v1_funct_1(sK0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_23,negated_conjecture,
% 2.44/0.99      ( v1_funct_1(sK0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_118,plain,
% 2.44/0.99      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/0.99      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_22,c_23]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_119,negated_conjecture,
% 2.44/0.99      ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
% 2.44/0.99      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_118]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_340,plain,
% 2.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/0.99      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.44/0.99      | k1_relat_1(sK0) != X1
% 2.44/0.99      | k2_relat_1(sK0) != X2
% 2.44/0.99      | sK0 != X0
% 2.44/0.99      | k1_xboole_0 = X2 ),
% 2.44/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_119]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_341,plain,
% 2.44/0.99      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/0.99      | k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) != k1_relat_1(sK0)
% 2.44/0.99      | k1_xboole_0 = k2_relat_1(sK0) ),
% 2.44/0.99      inference(unflattening,[status(thm)],[c_340]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_14,plain,
% 2.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.44/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_349,plain,
% 2.44/0.99      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/0.99      | k1_xboole_0 = k2_relat_1(sK0) ),
% 2.44/0.99      inference(forward_subsumption_resolution,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_341,c_14]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_890,plain,
% 2.44/0.99      ( k1_xboole_0 = k2_relat_1(sK0)
% 2.44/0.99      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2070,plain,
% 2.44/0.99      ( k2_relat_1(sK0) = k1_xboole_0
% 2.44/0.99      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
% 2.44/0.99      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
% 2.44/0.99      | v1_relat_1(sK0) != iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_897,c_890]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_24,negated_conjecture,
% 2.44/0.99      ( v1_relat_1(sK0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_11,plain,
% 2.44/0.99      ( ~ r1_tarski(X0,X1)
% 2.44/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.44/0.99      | ~ v1_relat_1(X0)
% 2.44/0.99      | ~ v1_relat_1(X1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_9,plain,
% 2.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.44/0.99      | ~ v1_relat_1(X1)
% 2.44/0.99      | v1_relat_1(X0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_7,plain,
% 2.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_131,plain,
% 2.44/0.99      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.44/0.99      | ~ r1_tarski(X0,X1)
% 2.44/0.99      | ~ v1_relat_1(X1) ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_11,c_9,c_7]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_132,plain,
% 2.44/0.99      ( ~ r1_tarski(X0,X1)
% 2.44/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.44/0.99      | ~ v1_relat_1(X1) ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_131]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1041,plain,
% 2.44/0.99      ( ~ r1_tarski(X0,sK0)
% 2.44/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(sK0))
% 2.44/0.99      | ~ v1_relat_1(sK0) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_132]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1118,plain,
% 2.44/0.99      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
% 2.44/0.99      | ~ r1_tarski(sK0,sK0)
% 2.44/0.99      | ~ v1_relat_1(sK0) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1041]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2,plain,
% 2.44/0.99      ( r1_tarski(X0,X0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1119,plain,
% 2.44/0.99      ( r1_tarski(sK0,sK0) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1056,plain,
% 2.44/0.99      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.44/0.99      | ~ r1_tarski(k1_relat_1(sK0),X0)
% 2.44/0.99      | ~ r1_tarski(k2_relat_1(sK0),X1)
% 2.44/0.99      | ~ v1_relat_1(sK0) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1138,plain,
% 2.44/0.99      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),X0)))
% 2.44/0.99      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
% 2.44/0.99      | ~ r1_tarski(k2_relat_1(sK0),X0)
% 2.44/0.99      | ~ v1_relat_1(sK0) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1056]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1223,plain,
% 2.44/0.99      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/0.99      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
% 2.44/0.99      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
% 2.44/0.99      | ~ v1_relat_1(sK0) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1138]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1224,plain,
% 2.44/0.99      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_900,plain,
% 2.44/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.44/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1410,plain,
% 2.44/0.99      ( k2_relat_1(sK0) = k1_xboole_0
% 2.44/0.99      | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) != iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_900,c_890]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1415,plain,
% 2.44/0.99      ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
% 2.44/0.99      | k2_relat_1(sK0) = k1_xboole_0 ),
% 2.44/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1410]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_8,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1241,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X0)) | r1_tarski(sK0,X0) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1639,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/1.00      | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1241]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2121,plain,
% 2.44/1.00      ( k2_relat_1(sK0) = k1_xboole_0 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2070,c_24,c_1118,c_1119,c_1223,c_1224,c_1415,c_1639]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_902,plain,
% 2.44/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4,plain,
% 2.44/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.44/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2066,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.44/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 2.44/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_4,c_897]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2923,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 2.44/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_902,c_2066]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5545,plain,
% 2.44/1.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.44/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.44/1.00      | v1_relat_1(sK0) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2121,c_2923]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_25,plain,
% 2.44/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3,plain,
% 2.44/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_67,plain,
% 2.44/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_69,plain,
% 2.44/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_67]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5822,plain,
% 2.44/1.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_5545,c_25,c_69]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_16,plain,
% 2.44/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.44/1.00      | k1_xboole_0 = X0 ),
% 2.44/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_297,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.44/1.00      | k1_relat_1(sK0) != X0
% 2.44/1.00      | k2_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | k1_xboole_0 = X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_119]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_298,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
% 2.44/1.00      | k2_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | k1_xboole_0 = k1_relat_1(sK0) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_297]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_892,plain,
% 2.44/1.00      ( k2_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | k1_xboole_0 = k1_relat_1(sK0)
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.44/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_981,plain,
% 2.44/1.00      ( k1_relat_1(sK0) = k1_xboole_0
% 2.44/1.00      | k2_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.44/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_892,c_4]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_62,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.44/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_64,plain,
% 2.44/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.44/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_62]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1067,plain,
% 2.44/1.00      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | k2_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | k1_relat_1(sK0) = k1_xboole_0 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_981,c_64,c_69]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1068,plain,
% 2.44/1.00      ( k1_relat_1(sK0) = k1_xboole_0
% 2.44/1.00      | k2_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_1067]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2124,plain,
% 2.44/1.00      ( k1_relat_1(sK0) = k1_xboole_0
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | k1_xboole_0 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_2121,c_1068]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2135,plain,
% 2.44/1.00      ( k1_relat_1(sK0) = k1_xboole_0
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top ),
% 2.44/1.00      inference(equality_resolution_simp,[status(thm)],[c_2124]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2139,plain,
% 2.44/1.00      ( k1_relat_1(sK0) = k1_xboole_0
% 2.44/1.00      | sK0 != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_2135,c_4]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_0,plain,
% 2.44/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.44/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1080,plain,
% 2.44/1.00      ( ~ r1_tarski(sK0,k1_xboole_0)
% 2.44/1.00      | ~ r1_tarski(k1_xboole_0,sK0)
% 2.44/1.00      | sK0 = k1_xboole_0 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1081,plain,
% 2.44/1.00      ( sK0 = k1_xboole_0
% 2.44/1.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 2.44/1.00      | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1080]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1097,plain,
% 2.44/1.00      ( r1_tarski(k1_xboole_0,sK0) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1100,plain,
% 2.44/1.00      ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1097]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1120,plain,
% 2.44/1.00      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) = iProver_top
% 2.44/1.00      | r1_tarski(sK0,sK0) != iProver_top
% 2.44/1.00      | v1_relat_1(sK0) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1118]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1122,plain,
% 2.44/1.00      ( r1_tarski(sK0,sK0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1119]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1151,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
% 2.44/1.00      | r1_tarski(sK0,k1_xboole_0) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1152,plain,
% 2.44/1.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.44/1.00      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1225,plain,
% 2.44/1.00      ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) = iProver_top
% 2.44/1.00      | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) != iProver_top
% 2.44/1.00      | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) != iProver_top
% 2.44/1.00      | v1_relat_1(sK0) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1223]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1227,plain,
% 2.44/1.00      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1224]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2476,plain,
% 2.44/1.00      ( k1_relat_1(sK0) = k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2139,c_24,c_25,c_1068,c_1081,c_1100,c_1118,c_1120,
% 2.44/1.00                 c_1119,c_1122,c_1152,c_1223,c_1225,c_1224,c_1227,c_1415,
% 2.44/1.00                 c_1639]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5828,plain,
% 2.44/1.00      ( k1_relat_1(sK0) = k1_xboole_0 ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_5822,c_2476]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5,plain,
% 2.44/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.44/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_898,plain,
% 2.44/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.44/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1587,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 2.44/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_5,c_898]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5829,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,X0,sK0) = k1_relat_1(sK0) ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_5822,c_1587]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5836,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,X0,sK0) = k1_xboole_0 ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_5828,c_5829]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_5846,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) = k1_xboole_0 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_5836]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_18,plain,
% 2.44/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.44/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.44/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_324,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.44/1.00      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.44/1.00      | k1_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | k2_relat_1(sK0) != X1
% 2.44/1.00      | sK0 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_119]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_325,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
% 2.44/1.00      | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))
% 2.44/1.00      | k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.44/1.00      | k1_relat_1(sK0) != k1_xboole_0 ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_324]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_891,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.44/1.00      | k1_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_972,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK0),sK0) != k1_xboole_0
% 2.44/1.00      | k1_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_891,c_5]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2125,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.44/1.00      | k1_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_2121,c_972]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2131,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.44/1.00      | k1_relat_1(sK0) != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/1.00      inference(demodulation,[status(thm)],[c_2125,c_4]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2358,plain,
% 2.44/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK0) != k1_xboole_0
% 2.44/1.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2131,c_24,c_25,c_1068,c_1081,c_1100,c_1118,c_1120,
% 2.44/1.00                 c_1119,c_1122,c_1152,c_1223,c_1225,c_1224,c_1227,c_1415,
% 2.44/1.00                 c_1639]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(contradiction,plain,
% 2.44/1.00      ( $false ),
% 2.44/1.00      inference(minisat,[status(thm)],[c_5846,c_5545,c_2358,c_69,c_25]) ).
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  ------                               Statistics
% 2.44/1.00  
% 2.44/1.00  ------ General
% 2.44/1.00  
% 2.44/1.00  abstr_ref_over_cycles:                  0
% 2.44/1.00  abstr_ref_under_cycles:                 0
% 2.44/1.00  gc_basic_clause_elim:                   0
% 2.44/1.00  forced_gc_time:                         0
% 2.44/1.00  parsing_time:                           0.008
% 2.44/1.00  unif_index_cands_time:                  0.
% 2.44/1.00  unif_index_add_time:                    0.
% 2.44/1.00  orderings_time:                         0.
% 2.44/1.00  out_proof_time:                         0.011
% 2.44/1.00  total_time:                             0.21
% 2.44/1.00  num_of_symbols:                         43
% 2.44/1.00  num_of_terms:                           4108
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing
% 2.44/1.00  
% 2.44/1.00  num_of_splits:                          0
% 2.44/1.00  num_of_split_atoms:                     0
% 2.44/1.00  num_of_reused_defs:                     0
% 2.44/1.00  num_eq_ax_congr_red:                    2
% 2.44/1.00  num_of_sem_filtered_clauses:            2
% 2.44/1.00  num_of_subtypes:                        0
% 2.44/1.00  monotx_restored_types:                  0
% 2.44/1.00  sat_num_of_epr_types:                   0
% 2.44/1.00  sat_num_of_non_cyclic_types:            0
% 2.44/1.00  sat_guarded_non_collapsed_types:        0
% 2.44/1.00  num_pure_diseq_elim:                    0
% 2.44/1.00  simp_replaced_by:                       0
% 2.44/1.00  res_preprocessed:                       102
% 2.44/1.00  prep_upred:                             0
% 2.44/1.00  prep_unflattend:                        26
% 2.44/1.00  smt_new_axioms:                         0
% 2.44/1.00  pred_elim_cands:                        3
% 2.44/1.00  pred_elim:                              1
% 2.44/1.00  pred_elim_cl:                           4
% 2.44/1.00  pred_elim_cycles:                       3
% 2.44/1.00  merged_defs:                            8
% 2.44/1.00  merged_defs_ncl:                        0
% 2.44/1.00  bin_hyper_res:                          9
% 2.44/1.00  prep_cycles:                            4
% 2.44/1.00  pred_elim_time:                         0.002
% 2.44/1.00  splitting_time:                         0.
% 2.44/1.00  sem_filter_time:                        0.
% 2.44/1.00  monotx_time:                            0.
% 2.44/1.00  subtype_inf_time:                       0.
% 2.44/1.00  
% 2.44/1.00  ------ Problem properties
% 2.44/1.00  
% 2.44/1.00  clauses:                                19
% 2.44/1.00  conjectures:                            1
% 2.44/1.00  epr:                                    5
% 2.44/1.00  horn:                                   18
% 2.44/1.00  ground:                                 6
% 2.44/1.00  unary:                                  7
% 2.44/1.00  binary:                                 4
% 2.44/1.00  lits:                                   43
% 2.44/1.00  lits_eq:                                15
% 2.44/1.00  fd_pure:                                0
% 2.44/1.00  fd_pseudo:                              0
% 2.44/1.00  fd_cond:                                1
% 2.44/1.00  fd_pseudo_cond:                         1
% 2.44/1.00  ac_symbols:                             0
% 2.44/1.00  
% 2.44/1.00  ------ Propositional Solver
% 2.44/1.00  
% 2.44/1.00  prop_solver_calls:                      30
% 2.44/1.00  prop_fast_solver_calls:                 728
% 2.44/1.00  smt_solver_calls:                       0
% 2.44/1.00  smt_fast_solver_calls:                  0
% 2.44/1.00  prop_num_of_clauses:                    1954
% 2.44/1.00  prop_preprocess_simplified:             4936
% 2.44/1.00  prop_fo_subsumed:                       23
% 2.44/1.00  prop_solver_time:                       0.
% 2.44/1.00  smt_solver_time:                        0.
% 2.44/1.00  smt_fast_solver_time:                   0.
% 2.44/1.00  prop_fast_solver_time:                  0.
% 2.44/1.00  prop_unsat_core_time:                   0.
% 2.44/1.00  
% 2.44/1.00  ------ QBF
% 2.44/1.00  
% 2.44/1.00  qbf_q_res:                              0
% 2.44/1.00  qbf_num_tautologies:                    0
% 2.44/1.00  qbf_prep_cycles:                        0
% 2.44/1.00  
% 2.44/1.00  ------ BMC1
% 2.44/1.00  
% 2.44/1.00  bmc1_current_bound:                     -1
% 2.44/1.00  bmc1_last_solved_bound:                 -1
% 2.44/1.00  bmc1_unsat_core_size:                   -1
% 2.44/1.00  bmc1_unsat_core_parents_size:           -1
% 2.44/1.00  bmc1_merge_next_fun:                    0
% 2.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation
% 2.44/1.00  
% 2.44/1.00  inst_num_of_clauses:                    526
% 2.44/1.00  inst_num_in_passive:                    264
% 2.44/1.00  inst_num_in_active:                     250
% 2.44/1.00  inst_num_in_unprocessed:                14
% 2.44/1.00  inst_num_of_loops:                      380
% 2.44/1.00  inst_num_of_learning_restarts:          0
% 2.44/1.00  inst_num_moves_active_passive:          126
% 2.44/1.00  inst_lit_activity:                      0
% 2.44/1.00  inst_lit_activity_moves:                0
% 2.44/1.00  inst_num_tautologies:                   0
% 2.44/1.00  inst_num_prop_implied:                  0
% 2.44/1.00  inst_num_existing_simplified:           0
% 2.44/1.00  inst_num_eq_res_simplified:             0
% 2.44/1.00  inst_num_child_elim:                    0
% 2.44/1.00  inst_num_of_dismatching_blockings:      332
% 2.44/1.00  inst_num_of_non_proper_insts:           890
% 2.44/1.00  inst_num_of_duplicates:                 0
% 2.44/1.00  inst_inst_num_from_inst_to_res:         0
% 2.44/1.00  inst_dismatching_checking_time:         0.
% 2.44/1.00  
% 2.44/1.00  ------ Resolution
% 2.44/1.00  
% 2.44/1.00  res_num_of_clauses:                     0
% 2.44/1.00  res_num_in_passive:                     0
% 2.44/1.00  res_num_in_active:                      0
% 2.44/1.00  res_num_of_loops:                       106
% 2.44/1.00  res_forward_subset_subsumed:            55
% 2.44/1.00  res_backward_subset_subsumed:           6
% 2.44/1.00  res_forward_subsumed:                   0
% 2.44/1.00  res_backward_subsumed:                  0
% 2.44/1.00  res_forward_subsumption_resolution:     1
% 2.44/1.00  res_backward_subsumption_resolution:    0
% 2.44/1.00  res_clause_to_clause_subsumption:       608
% 2.44/1.00  res_orphan_elimination:                 0
% 2.44/1.00  res_tautology_del:                      49
% 2.44/1.00  res_num_eq_res_simplified:              0
% 2.44/1.00  res_num_sel_changes:                    0
% 2.44/1.00  res_moves_from_active_to_pass:          0
% 2.44/1.00  
% 2.44/1.00  ------ Superposition
% 2.44/1.00  
% 2.44/1.00  sup_time_total:                         0.
% 2.44/1.00  sup_time_generating:                    0.
% 2.44/1.00  sup_time_sim_full:                      0.
% 2.44/1.00  sup_time_sim_immed:                     0.
% 2.44/1.00  
% 2.44/1.00  sup_num_of_clauses:                     102
% 2.44/1.00  sup_num_in_active:                      66
% 2.44/1.00  sup_num_in_passive:                     36
% 2.44/1.00  sup_num_of_loops:                       74
% 2.44/1.00  sup_fw_superposition:                   167
% 2.44/1.00  sup_bw_superposition:                   24
% 2.44/1.00  sup_immediate_simplified:               71
% 2.44/1.00  sup_given_eliminated:                   2
% 2.44/1.00  comparisons_done:                       0
% 2.44/1.00  comparisons_avoided:                    0
% 2.44/1.00  
% 2.44/1.00  ------ Simplifications
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  sim_fw_subset_subsumed:                 4
% 2.44/1.00  sim_bw_subset_subsumed:                 6
% 2.44/1.00  sim_fw_subsumed:                        29
% 2.44/1.00  sim_bw_subsumed:                        6
% 2.44/1.00  sim_fw_subsumption_res:                 1
% 2.44/1.00  sim_bw_subsumption_res:                 0
% 2.44/1.00  sim_tautology_del:                      5
% 2.44/1.00  sim_eq_tautology_del:                   34
% 2.44/1.00  sim_eq_res_simp:                        1
% 2.44/1.00  sim_fw_demodulated:                     4
% 2.44/1.00  sim_bw_demodulated:                     5
% 2.44/1.00  sim_light_normalised:                   54
% 2.44/1.00  sim_joinable_taut:                      0
% 2.44/1.00  sim_joinable_simp:                      0
% 2.44/1.00  sim_ac_normalised:                      0
% 2.44/1.00  sim_smt_subsumption:                    0
% 2.44/1.00  
%------------------------------------------------------------------------------
