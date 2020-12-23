%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:12 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  135 (1029 expanded)
%              Number of clauses        :   84 ( 351 expanded)
%              Number of leaves         :   16 ( 190 expanded)
%              Depth                    :   25
%              Number of atoms          :  379 (4573 expanded)
%              Number of equality atoms :  185 ( 956 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f37,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,
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

fof(f39,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
      | ~ v1_funct_1(sK2) )
    & r1_tarski(k2_relat_1(sK2),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f38])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_154,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_26])).

cnf(c_155,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK2) != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_155])).

cnf(c_483,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_491,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_xboole_0 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_483,c_16])).

cnf(c_1036,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_392,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_393,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK2),X1)
    | ~ r1_tarski(k1_relat_1(sK2),X0) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_1157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_1237,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1238,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1259,plain,
    ( k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1036,c_25,c_491,c_1237,c_1238])).

cnf(c_1041,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1264,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1259,c_1041])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_358,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_1040,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_1860,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1040])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1048,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1870,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1860,c_1048])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_415,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_416,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_563,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_416])).

cnf(c_1912,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1870,c_563])).

cnf(c_1928,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1912])).

cnf(c_1038,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_1915,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1870,c_1038])).

cnf(c_1931,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1928,c_1915])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1513,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1045,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1632,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1513,c_1045])).

cnf(c_2276,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1931,c_1632])).

cnf(c_2282,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2276,c_1632])).

cnf(c_1042,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2287,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2282,c_1042])).

cnf(c_2395,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2287,c_1928])).

cnf(c_2397,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2395])).

cnf(c_1437,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1438,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1437])).

cnf(c_1359,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_1361,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_1363,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_155])).

cnf(c_467,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_602,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(bin_hyper_res,[status(thm)],[c_467,c_563])).

cnf(c_1035,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_1263,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1259,c_1035])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_82,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_81,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_83,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_86,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_394,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_396,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_660,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1253,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK2),X2)
    | X2 != X1
    | k1_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_1254,plain,
    ( X0 != X1
    | k1_relat_1(sK2) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_1256,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_1346,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1263,c_82,c_83,c_86,c_396,c_416,c_1256,c_1264])).

cnf(c_1347,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1346])).

cnf(c_657,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1324,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_658,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1230,plain,
    ( k2_relat_1(sK2) != X0
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_1323,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_1241,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2397,c_1860,c_1438,c_1363,c_1347,c_1324,c_1323,c_1264,c_1241])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.16/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.04  
% 2.16/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.04  
% 2.16/1.04  ------  iProver source info
% 2.16/1.04  
% 2.16/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.04  git: non_committed_changes: false
% 2.16/1.04  git: last_make_outside_of_git: false
% 2.16/1.04  
% 2.16/1.04  ------ 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options
% 2.16/1.04  
% 2.16/1.04  --out_options                           all
% 2.16/1.04  --tptp_safe_out                         true
% 2.16/1.04  --problem_path                          ""
% 2.16/1.04  --include_path                          ""
% 2.16/1.04  --clausifier                            res/vclausify_rel
% 2.16/1.04  --clausifier_options                    --mode clausify
% 2.16/1.04  --stdin                                 false
% 2.16/1.04  --stats_out                             all
% 2.16/1.04  
% 2.16/1.04  ------ General Options
% 2.16/1.04  
% 2.16/1.04  --fof                                   false
% 2.16/1.04  --time_out_real                         305.
% 2.16/1.04  --time_out_virtual                      -1.
% 2.16/1.04  --symbol_type_check                     false
% 2.16/1.04  --clausify_out                          false
% 2.16/1.04  --sig_cnt_out                           false
% 2.16/1.04  --trig_cnt_out                          false
% 2.16/1.04  --trig_cnt_out_tolerance                1.
% 2.16/1.04  --trig_cnt_out_sk_spl                   false
% 2.16/1.04  --abstr_cl_out                          false
% 2.16/1.04  
% 2.16/1.04  ------ Global Options
% 2.16/1.04  
% 2.16/1.04  --schedule                              default
% 2.16/1.04  --add_important_lit                     false
% 2.16/1.04  --prop_solver_per_cl                    1000
% 2.16/1.04  --min_unsat_core                        false
% 2.16/1.04  --soft_assumptions                      false
% 2.16/1.04  --soft_lemma_size                       3
% 2.16/1.04  --prop_impl_unit_size                   0
% 2.16/1.04  --prop_impl_unit                        []
% 2.16/1.04  --share_sel_clauses                     true
% 2.16/1.04  --reset_solvers                         false
% 2.16/1.04  --bc_imp_inh                            [conj_cone]
% 2.16/1.04  --conj_cone_tolerance                   3.
% 2.16/1.04  --extra_neg_conj                        none
% 2.16/1.04  --large_theory_mode                     true
% 2.16/1.04  --prolific_symb_bound                   200
% 2.16/1.04  --lt_threshold                          2000
% 2.16/1.04  --clause_weak_htbl                      true
% 2.16/1.04  --gc_record_bc_elim                     false
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing Options
% 2.16/1.04  
% 2.16/1.04  --preprocessing_flag                    true
% 2.16/1.04  --time_out_prep_mult                    0.1
% 2.16/1.04  --splitting_mode                        input
% 2.16/1.04  --splitting_grd                         true
% 2.16/1.04  --splitting_cvd                         false
% 2.16/1.04  --splitting_cvd_svl                     false
% 2.16/1.04  --splitting_nvd                         32
% 2.16/1.04  --sub_typing                            true
% 2.16/1.04  --prep_gs_sim                           true
% 2.16/1.04  --prep_unflatten                        true
% 2.16/1.04  --prep_res_sim                          true
% 2.16/1.04  --prep_upred                            true
% 2.16/1.04  --prep_sem_filter                       exhaustive
% 2.16/1.04  --prep_sem_filter_out                   false
% 2.16/1.04  --pred_elim                             true
% 2.16/1.04  --res_sim_input                         true
% 2.16/1.04  --eq_ax_congr_red                       true
% 2.16/1.04  --pure_diseq_elim                       true
% 2.16/1.04  --brand_transform                       false
% 2.16/1.04  --non_eq_to_eq                          false
% 2.16/1.04  --prep_def_merge                        true
% 2.16/1.04  --prep_def_merge_prop_impl              false
% 2.16/1.04  --prep_def_merge_mbd                    true
% 2.16/1.04  --prep_def_merge_tr_red                 false
% 2.16/1.04  --prep_def_merge_tr_cl                  false
% 2.16/1.04  --smt_preprocessing                     true
% 2.16/1.04  --smt_ac_axioms                         fast
% 2.16/1.04  --preprocessed_out                      false
% 2.16/1.04  --preprocessed_stats                    false
% 2.16/1.04  
% 2.16/1.04  ------ Abstraction refinement Options
% 2.16/1.04  
% 2.16/1.04  --abstr_ref                             []
% 2.16/1.04  --abstr_ref_prep                        false
% 2.16/1.04  --abstr_ref_until_sat                   false
% 2.16/1.04  --abstr_ref_sig_restrict                funpre
% 2.16/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.04  --abstr_ref_under                       []
% 2.16/1.04  
% 2.16/1.04  ------ SAT Options
% 2.16/1.04  
% 2.16/1.04  --sat_mode                              false
% 2.16/1.04  --sat_fm_restart_options                ""
% 2.16/1.04  --sat_gr_def                            false
% 2.16/1.04  --sat_epr_types                         true
% 2.16/1.04  --sat_non_cyclic_types                  false
% 2.16/1.04  --sat_finite_models                     false
% 2.16/1.04  --sat_fm_lemmas                         false
% 2.16/1.04  --sat_fm_prep                           false
% 2.16/1.04  --sat_fm_uc_incr                        true
% 2.16/1.04  --sat_out_model                         small
% 2.16/1.04  --sat_out_clauses                       false
% 2.16/1.04  
% 2.16/1.04  ------ QBF Options
% 2.16/1.04  
% 2.16/1.04  --qbf_mode                              false
% 2.16/1.04  --qbf_elim_univ                         false
% 2.16/1.04  --qbf_dom_inst                          none
% 2.16/1.04  --qbf_dom_pre_inst                      false
% 2.16/1.04  --qbf_sk_in                             false
% 2.16/1.04  --qbf_pred_elim                         true
% 2.16/1.04  --qbf_split                             512
% 2.16/1.04  
% 2.16/1.04  ------ BMC1 Options
% 2.16/1.04  
% 2.16/1.04  --bmc1_incremental                      false
% 2.16/1.04  --bmc1_axioms                           reachable_all
% 2.16/1.04  --bmc1_min_bound                        0
% 2.16/1.04  --bmc1_max_bound                        -1
% 2.16/1.04  --bmc1_max_bound_default                -1
% 2.16/1.04  --bmc1_symbol_reachability              true
% 2.16/1.04  --bmc1_property_lemmas                  false
% 2.16/1.04  --bmc1_k_induction                      false
% 2.16/1.04  --bmc1_non_equiv_states                 false
% 2.16/1.04  --bmc1_deadlock                         false
% 2.16/1.04  --bmc1_ucm                              false
% 2.16/1.04  --bmc1_add_unsat_core                   none
% 2.16/1.04  --bmc1_unsat_core_children              false
% 2.16/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.04  --bmc1_out_stat                         full
% 2.16/1.04  --bmc1_ground_init                      false
% 2.16/1.04  --bmc1_pre_inst_next_state              false
% 2.16/1.04  --bmc1_pre_inst_state                   false
% 2.16/1.04  --bmc1_pre_inst_reach_state             false
% 2.16/1.04  --bmc1_out_unsat_core                   false
% 2.16/1.04  --bmc1_aig_witness_out                  false
% 2.16/1.04  --bmc1_verbose                          false
% 2.16/1.04  --bmc1_dump_clauses_tptp                false
% 2.16/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.04  --bmc1_dump_file                        -
% 2.16/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.04  --bmc1_ucm_extend_mode                  1
% 2.16/1.04  --bmc1_ucm_init_mode                    2
% 2.16/1.04  --bmc1_ucm_cone_mode                    none
% 2.16/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.04  --bmc1_ucm_relax_model                  4
% 2.16/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.04  --bmc1_ucm_layered_model                none
% 2.16/1.04  --bmc1_ucm_max_lemma_size               10
% 2.16/1.04  
% 2.16/1.04  ------ AIG Options
% 2.16/1.04  
% 2.16/1.04  --aig_mode                              false
% 2.16/1.04  
% 2.16/1.04  ------ Instantiation Options
% 2.16/1.04  
% 2.16/1.04  --instantiation_flag                    true
% 2.16/1.04  --inst_sos_flag                         false
% 2.16/1.04  --inst_sos_phase                        true
% 2.16/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.04  --inst_lit_sel_side                     num_symb
% 2.16/1.04  --inst_solver_per_active                1400
% 2.16/1.04  --inst_solver_calls_frac                1.
% 2.16/1.04  --inst_passive_queue_type               priority_queues
% 2.16/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.04  --inst_passive_queues_freq              [25;2]
% 2.16/1.04  --inst_dismatching                      true
% 2.16/1.04  --inst_eager_unprocessed_to_passive     true
% 2.16/1.04  --inst_prop_sim_given                   true
% 2.16/1.04  --inst_prop_sim_new                     false
% 2.16/1.04  --inst_subs_new                         false
% 2.16/1.04  --inst_eq_res_simp                      false
% 2.16/1.04  --inst_subs_given                       false
% 2.16/1.04  --inst_orphan_elimination               true
% 2.16/1.04  --inst_learning_loop_flag               true
% 2.16/1.04  --inst_learning_start                   3000
% 2.16/1.04  --inst_learning_factor                  2
% 2.16/1.04  --inst_start_prop_sim_after_learn       3
% 2.16/1.04  --inst_sel_renew                        solver
% 2.16/1.04  --inst_lit_activity_flag                true
% 2.16/1.04  --inst_restr_to_given                   false
% 2.16/1.04  --inst_activity_threshold               500
% 2.16/1.04  --inst_out_proof                        true
% 2.16/1.04  
% 2.16/1.04  ------ Resolution Options
% 2.16/1.04  
% 2.16/1.04  --resolution_flag                       true
% 2.16/1.04  --res_lit_sel                           adaptive
% 2.16/1.04  --res_lit_sel_side                      none
% 2.16/1.04  --res_ordering                          kbo
% 2.16/1.04  --res_to_prop_solver                    active
% 2.16/1.04  --res_prop_simpl_new                    false
% 2.16/1.04  --res_prop_simpl_given                  true
% 2.16/1.04  --res_passive_queue_type                priority_queues
% 2.16/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.04  --res_passive_queues_freq               [15;5]
% 2.16/1.04  --res_forward_subs                      full
% 2.16/1.04  --res_backward_subs                     full
% 2.16/1.04  --res_forward_subs_resolution           true
% 2.16/1.04  --res_backward_subs_resolution          true
% 2.16/1.04  --res_orphan_elimination                true
% 2.16/1.04  --res_time_limit                        2.
% 2.16/1.04  --res_out_proof                         true
% 2.16/1.04  
% 2.16/1.04  ------ Superposition Options
% 2.16/1.04  
% 2.16/1.04  --superposition_flag                    true
% 2.16/1.04  --sup_passive_queue_type                priority_queues
% 2.16/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.04  --demod_completeness_check              fast
% 2.16/1.04  --demod_use_ground                      true
% 2.16/1.04  --sup_to_prop_solver                    passive
% 2.16/1.04  --sup_prop_simpl_new                    true
% 2.16/1.04  --sup_prop_simpl_given                  true
% 2.16/1.04  --sup_fun_splitting                     false
% 2.16/1.04  --sup_smt_interval                      50000
% 2.16/1.04  
% 2.16/1.04  ------ Superposition Simplification Setup
% 2.16/1.04  
% 2.16/1.04  --sup_indices_passive                   []
% 2.16/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_full_bw                           [BwDemod]
% 2.16/1.04  --sup_immed_triv                        [TrivRules]
% 2.16/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_immed_bw_main                     []
% 2.16/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.04  
% 2.16/1.04  ------ Combination Options
% 2.16/1.04  
% 2.16/1.04  --comb_res_mult                         3
% 2.16/1.04  --comb_sup_mult                         2
% 2.16/1.04  --comb_inst_mult                        10
% 2.16/1.04  
% 2.16/1.04  ------ Debug Options
% 2.16/1.04  
% 2.16/1.04  --dbg_backtrace                         false
% 2.16/1.04  --dbg_dump_prop_clauses                 false
% 2.16/1.04  --dbg_dump_prop_clauses_file            -
% 2.16/1.04  --dbg_out_stat                          false
% 2.16/1.04  ------ Parsing...
% 2.16/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.04  
% 2.16/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.04  ------ Proving...
% 2.16/1.04  ------ Problem Properties 
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  clauses                                 18
% 2.16/1.04  conjectures                             1
% 2.16/1.04  EPR                                     5
% 2.16/1.04  Horn                                    18
% 2.16/1.04  unary                                   5
% 2.16/1.04  binary                                  8
% 2.16/1.04  lits                                    39
% 2.16/1.04  lits eq                                 15
% 2.16/1.04  fd_pure                                 0
% 2.16/1.04  fd_pseudo                               0
% 2.16/1.04  fd_cond                                 1
% 2.16/1.04  fd_pseudo_cond                          1
% 2.16/1.04  AC symbols                              0
% 2.16/1.04  
% 2.16/1.04  ------ Schedule dynamic 5 is on 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.04  
% 2.16/1.04  
% 2.16/1.04  ------ 
% 2.16/1.04  Current options:
% 2.16/1.04  ------ 
% 2.16/1.04  
% 2.16/1.04  ------ Input Options
% 2.16/1.04  
% 2.16/1.04  --out_options                           all
% 2.16/1.04  --tptp_safe_out                         true
% 2.16/1.04  --problem_path                          ""
% 2.16/1.04  --include_path                          ""
% 2.16/1.04  --clausifier                            res/vclausify_rel
% 2.16/1.04  --clausifier_options                    --mode clausify
% 2.16/1.04  --stdin                                 false
% 2.16/1.04  --stats_out                             all
% 2.16/1.05  
% 2.16/1.05  ------ General Options
% 2.16/1.05  
% 2.16/1.05  --fof                                   false
% 2.16/1.05  --time_out_real                         305.
% 2.16/1.05  --time_out_virtual                      -1.
% 2.16/1.05  --symbol_type_check                     false
% 2.16/1.05  --clausify_out                          false
% 2.16/1.05  --sig_cnt_out                           false
% 2.16/1.05  --trig_cnt_out                          false
% 2.16/1.05  --trig_cnt_out_tolerance                1.
% 2.16/1.05  --trig_cnt_out_sk_spl                   false
% 2.16/1.05  --abstr_cl_out                          false
% 2.16/1.05  
% 2.16/1.05  ------ Global Options
% 2.16/1.05  
% 2.16/1.05  --schedule                              default
% 2.16/1.05  --add_important_lit                     false
% 2.16/1.05  --prop_solver_per_cl                    1000
% 2.16/1.05  --min_unsat_core                        false
% 2.16/1.05  --soft_assumptions                      false
% 2.16/1.05  --soft_lemma_size                       3
% 2.16/1.05  --prop_impl_unit_size                   0
% 2.16/1.05  --prop_impl_unit                        []
% 2.16/1.05  --share_sel_clauses                     true
% 2.16/1.05  --reset_solvers                         false
% 2.16/1.05  --bc_imp_inh                            [conj_cone]
% 2.16/1.05  --conj_cone_tolerance                   3.
% 2.16/1.05  --extra_neg_conj                        none
% 2.16/1.05  --large_theory_mode                     true
% 2.16/1.05  --prolific_symb_bound                   200
% 2.16/1.05  --lt_threshold                          2000
% 2.16/1.05  --clause_weak_htbl                      true
% 2.16/1.05  --gc_record_bc_elim                     false
% 2.16/1.05  
% 2.16/1.05  ------ Preprocessing Options
% 2.16/1.05  
% 2.16/1.05  --preprocessing_flag                    true
% 2.16/1.05  --time_out_prep_mult                    0.1
% 2.16/1.05  --splitting_mode                        input
% 2.16/1.05  --splitting_grd                         true
% 2.16/1.05  --splitting_cvd                         false
% 2.16/1.05  --splitting_cvd_svl                     false
% 2.16/1.05  --splitting_nvd                         32
% 2.16/1.05  --sub_typing                            true
% 2.16/1.05  --prep_gs_sim                           true
% 2.16/1.05  --prep_unflatten                        true
% 2.16/1.05  --prep_res_sim                          true
% 2.16/1.05  --prep_upred                            true
% 2.16/1.05  --prep_sem_filter                       exhaustive
% 2.16/1.05  --prep_sem_filter_out                   false
% 2.16/1.05  --pred_elim                             true
% 2.16/1.05  --res_sim_input                         true
% 2.16/1.05  --eq_ax_congr_red                       true
% 2.16/1.05  --pure_diseq_elim                       true
% 2.16/1.05  --brand_transform                       false
% 2.16/1.05  --non_eq_to_eq                          false
% 2.16/1.05  --prep_def_merge                        true
% 2.16/1.05  --prep_def_merge_prop_impl              false
% 2.16/1.05  --prep_def_merge_mbd                    true
% 2.16/1.05  --prep_def_merge_tr_red                 false
% 2.16/1.05  --prep_def_merge_tr_cl                  false
% 2.16/1.05  --smt_preprocessing                     true
% 2.16/1.05  --smt_ac_axioms                         fast
% 2.16/1.05  --preprocessed_out                      false
% 2.16/1.05  --preprocessed_stats                    false
% 2.16/1.05  
% 2.16/1.05  ------ Abstraction refinement Options
% 2.16/1.05  
% 2.16/1.05  --abstr_ref                             []
% 2.16/1.05  --abstr_ref_prep                        false
% 2.16/1.05  --abstr_ref_until_sat                   false
% 2.16/1.05  --abstr_ref_sig_restrict                funpre
% 2.16/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.05  --abstr_ref_under                       []
% 2.16/1.05  
% 2.16/1.05  ------ SAT Options
% 2.16/1.05  
% 2.16/1.05  --sat_mode                              false
% 2.16/1.05  --sat_fm_restart_options                ""
% 2.16/1.05  --sat_gr_def                            false
% 2.16/1.05  --sat_epr_types                         true
% 2.16/1.05  --sat_non_cyclic_types                  false
% 2.16/1.05  --sat_finite_models                     false
% 2.16/1.05  --sat_fm_lemmas                         false
% 2.16/1.05  --sat_fm_prep                           false
% 2.16/1.05  --sat_fm_uc_incr                        true
% 2.16/1.05  --sat_out_model                         small
% 2.16/1.05  --sat_out_clauses                       false
% 2.16/1.05  
% 2.16/1.05  ------ QBF Options
% 2.16/1.05  
% 2.16/1.05  --qbf_mode                              false
% 2.16/1.05  --qbf_elim_univ                         false
% 2.16/1.05  --qbf_dom_inst                          none
% 2.16/1.05  --qbf_dom_pre_inst                      false
% 2.16/1.05  --qbf_sk_in                             false
% 2.16/1.05  --qbf_pred_elim                         true
% 2.16/1.05  --qbf_split                             512
% 2.16/1.05  
% 2.16/1.05  ------ BMC1 Options
% 2.16/1.05  
% 2.16/1.05  --bmc1_incremental                      false
% 2.16/1.05  --bmc1_axioms                           reachable_all
% 2.16/1.05  --bmc1_min_bound                        0
% 2.16/1.05  --bmc1_max_bound                        -1
% 2.16/1.05  --bmc1_max_bound_default                -1
% 2.16/1.05  --bmc1_symbol_reachability              true
% 2.16/1.05  --bmc1_property_lemmas                  false
% 2.16/1.05  --bmc1_k_induction                      false
% 2.16/1.05  --bmc1_non_equiv_states                 false
% 2.16/1.05  --bmc1_deadlock                         false
% 2.16/1.05  --bmc1_ucm                              false
% 2.16/1.05  --bmc1_add_unsat_core                   none
% 2.16/1.05  --bmc1_unsat_core_children              false
% 2.16/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.05  --bmc1_out_stat                         full
% 2.16/1.05  --bmc1_ground_init                      false
% 2.16/1.05  --bmc1_pre_inst_next_state              false
% 2.16/1.05  --bmc1_pre_inst_state                   false
% 2.16/1.05  --bmc1_pre_inst_reach_state             false
% 2.16/1.05  --bmc1_out_unsat_core                   false
% 2.16/1.05  --bmc1_aig_witness_out                  false
% 2.16/1.05  --bmc1_verbose                          false
% 2.16/1.05  --bmc1_dump_clauses_tptp                false
% 2.16/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.05  --bmc1_dump_file                        -
% 2.16/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.05  --bmc1_ucm_extend_mode                  1
% 2.16/1.05  --bmc1_ucm_init_mode                    2
% 2.16/1.05  --bmc1_ucm_cone_mode                    none
% 2.16/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.05  --bmc1_ucm_relax_model                  4
% 2.16/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.05  --bmc1_ucm_layered_model                none
% 2.16/1.05  --bmc1_ucm_max_lemma_size               10
% 2.16/1.05  
% 2.16/1.05  ------ AIG Options
% 2.16/1.05  
% 2.16/1.05  --aig_mode                              false
% 2.16/1.05  
% 2.16/1.05  ------ Instantiation Options
% 2.16/1.05  
% 2.16/1.05  --instantiation_flag                    true
% 2.16/1.05  --inst_sos_flag                         false
% 2.16/1.05  --inst_sos_phase                        true
% 2.16/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.05  --inst_lit_sel_side                     none
% 2.16/1.05  --inst_solver_per_active                1400
% 2.16/1.05  --inst_solver_calls_frac                1.
% 2.16/1.05  --inst_passive_queue_type               priority_queues
% 2.16/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.05  --inst_passive_queues_freq              [25;2]
% 2.16/1.05  --inst_dismatching                      true
% 2.16/1.05  --inst_eager_unprocessed_to_passive     true
% 2.16/1.05  --inst_prop_sim_given                   true
% 2.16/1.05  --inst_prop_sim_new                     false
% 2.16/1.05  --inst_subs_new                         false
% 2.16/1.05  --inst_eq_res_simp                      false
% 2.16/1.05  --inst_subs_given                       false
% 2.16/1.05  --inst_orphan_elimination               true
% 2.16/1.05  --inst_learning_loop_flag               true
% 2.16/1.05  --inst_learning_start                   3000
% 2.16/1.05  --inst_learning_factor                  2
% 2.16/1.05  --inst_start_prop_sim_after_learn       3
% 2.16/1.05  --inst_sel_renew                        solver
% 2.16/1.05  --inst_lit_activity_flag                true
% 2.16/1.05  --inst_restr_to_given                   false
% 2.16/1.05  --inst_activity_threshold               500
% 2.16/1.05  --inst_out_proof                        true
% 2.16/1.05  
% 2.16/1.05  ------ Resolution Options
% 2.16/1.05  
% 2.16/1.05  --resolution_flag                       false
% 2.16/1.05  --res_lit_sel                           adaptive
% 2.16/1.05  --res_lit_sel_side                      none
% 2.16/1.05  --res_ordering                          kbo
% 2.16/1.05  --res_to_prop_solver                    active
% 2.16/1.05  --res_prop_simpl_new                    false
% 2.16/1.05  --res_prop_simpl_given                  true
% 2.16/1.05  --res_passive_queue_type                priority_queues
% 2.16/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.05  --res_passive_queues_freq               [15;5]
% 2.16/1.05  --res_forward_subs                      full
% 2.16/1.05  --res_backward_subs                     full
% 2.16/1.05  --res_forward_subs_resolution           true
% 2.16/1.05  --res_backward_subs_resolution          true
% 2.16/1.05  --res_orphan_elimination                true
% 2.16/1.05  --res_time_limit                        2.
% 2.16/1.05  --res_out_proof                         true
% 2.16/1.05  
% 2.16/1.05  ------ Superposition Options
% 2.16/1.05  
% 2.16/1.05  --superposition_flag                    true
% 2.16/1.05  --sup_passive_queue_type                priority_queues
% 2.16/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.05  --demod_completeness_check              fast
% 2.16/1.05  --demod_use_ground                      true
% 2.16/1.05  --sup_to_prop_solver                    passive
% 2.16/1.05  --sup_prop_simpl_new                    true
% 2.16/1.05  --sup_prop_simpl_given                  true
% 2.16/1.05  --sup_fun_splitting                     false
% 2.16/1.05  --sup_smt_interval                      50000
% 2.16/1.05  
% 2.16/1.05  ------ Superposition Simplification Setup
% 2.16/1.05  
% 2.16/1.05  --sup_indices_passive                   []
% 2.16/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.05  --sup_full_bw                           [BwDemod]
% 2.16/1.05  --sup_immed_triv                        [TrivRules]
% 2.16/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.05  --sup_immed_bw_main                     []
% 2.16/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.05  
% 2.16/1.05  ------ Combination Options
% 2.16/1.05  
% 2.16/1.05  --comb_res_mult                         3
% 2.16/1.05  --comb_sup_mult                         2
% 2.16/1.05  --comb_inst_mult                        10
% 2.16/1.05  
% 2.16/1.05  ------ Debug Options
% 2.16/1.05  
% 2.16/1.05  --dbg_backtrace                         false
% 2.16/1.05  --dbg_dump_prop_clauses                 false
% 2.16/1.05  --dbg_dump_prop_clauses_file            -
% 2.16/1.05  --dbg_out_stat                          false
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  ------ Proving...
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  % SZS status Theorem for theBenchmark.p
% 2.16/1.05  
% 2.16/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.05  
% 2.16/1.05  fof(f14,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f25,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(ennf_transformation,[],[f14])).
% 2.16/1.05  
% 2.16/1.05  fof(f26,plain,(
% 2.16/1.05    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(flattening,[],[f25])).
% 2.16/1.05  
% 2.16/1.05  fof(f37,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(nnf_transformation,[],[f26])).
% 2.16/1.05  
% 2.16/1.05  fof(f60,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f37])).
% 2.16/1.05  
% 2.16/1.05  fof(f15,conjecture,(
% 2.16/1.05    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f16,negated_conjecture,(
% 2.16/1.05    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.16/1.05    inference(negated_conjecture,[],[f15])).
% 2.16/1.05  
% 2.16/1.05  fof(f27,plain,(
% 2.16/1.05    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.16/1.05    inference(ennf_transformation,[],[f16])).
% 2.16/1.05  
% 2.16/1.05  fof(f28,plain,(
% 2.16/1.05    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.16/1.05    inference(flattening,[],[f27])).
% 2.16/1.05  
% 2.16/1.05  fof(f38,plain,(
% 2.16/1.05    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.16/1.05    introduced(choice_axiom,[])).
% 2.16/1.05  
% 2.16/1.05  fof(f39,plain,(
% 2.16/1.05    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.16/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f38])).
% 2.16/1.05  
% 2.16/1.05  fof(f67,plain,(
% 2.16/1.05    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)),
% 2.16/1.05    inference(cnf_transformation,[],[f39])).
% 2.16/1.05  
% 2.16/1.05  fof(f65,plain,(
% 2.16/1.05    v1_funct_1(sK2)),
% 2.16/1.05    inference(cnf_transformation,[],[f39])).
% 2.16/1.05  
% 2.16/1.05  fof(f12,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f22,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.05    inference(ennf_transformation,[],[f12])).
% 2.16/1.05  
% 2.16/1.05  fof(f56,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f22])).
% 2.16/1.05  
% 2.16/1.05  fof(f66,plain,(
% 2.16/1.05    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.16/1.05    inference(cnf_transformation,[],[f39])).
% 2.16/1.05  
% 2.16/1.05  fof(f13,axiom,(
% 2.16/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f23,plain,(
% 2.16/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.16/1.05    inference(ennf_transformation,[],[f13])).
% 2.16/1.05  
% 2.16/1.05  fof(f24,plain,(
% 2.16/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.16/1.05    inference(flattening,[],[f23])).
% 2.16/1.05  
% 2.16/1.05  fof(f57,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f24])).
% 2.16/1.05  
% 2.16/1.05  fof(f64,plain,(
% 2.16/1.05    v1_relat_1(sK2)),
% 2.16/1.05    inference(cnf_transformation,[],[f39])).
% 2.16/1.05  
% 2.16/1.05  fof(f4,axiom,(
% 2.16/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f33,plain,(
% 2.16/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/1.05    inference(nnf_transformation,[],[f4])).
% 2.16/1.05  
% 2.16/1.05  fof(f34,plain,(
% 2.16/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.16/1.05    inference(flattening,[],[f33])).
% 2.16/1.05  
% 2.16/1.05  fof(f45,plain,(
% 2.16/1.05    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.16/1.05    inference(cnf_transformation,[],[f34])).
% 2.16/1.05  
% 2.16/1.05  fof(f68,plain,(
% 2.16/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.16/1.05    inference(equality_resolution,[],[f45])).
% 2.16/1.05  
% 2.16/1.05  fof(f6,axiom,(
% 2.16/1.05    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f48,plain,(
% 2.16/1.05    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f6])).
% 2.16/1.05  
% 2.16/1.05  fof(f7,axiom,(
% 2.16/1.05    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f18,plain,(
% 2.16/1.05    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.16/1.05    inference(ennf_transformation,[],[f7])).
% 2.16/1.05  
% 2.16/1.05  fof(f19,plain,(
% 2.16/1.05    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.16/1.05    inference(flattening,[],[f18])).
% 2.16/1.05  
% 2.16/1.05  fof(f49,plain,(
% 2.16/1.05    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f19])).
% 2.16/1.05  
% 2.16/1.05  fof(f3,axiom,(
% 2.16/1.05    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f17,plain,(
% 2.16/1.05    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.16/1.05    inference(ennf_transformation,[],[f3])).
% 2.16/1.05  
% 2.16/1.05  fof(f43,plain,(
% 2.16/1.05    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f17])).
% 2.16/1.05  
% 2.16/1.05  fof(f11,axiom,(
% 2.16/1.05    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f21,plain,(
% 2.16/1.05    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.16/1.05    inference(ennf_transformation,[],[f11])).
% 2.16/1.05  
% 2.16/1.05  fof(f36,plain,(
% 2.16/1.05    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.16/1.05    inference(nnf_transformation,[],[f21])).
% 2.16/1.05  
% 2.16/1.05  fof(f55,plain,(
% 2.16/1.05    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f36])).
% 2.16/1.05  
% 2.16/1.05  fof(f5,axiom,(
% 2.16/1.05    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f47,plain,(
% 2.16/1.05    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/1.05    inference(cnf_transformation,[],[f5])).
% 2.16/1.05  
% 2.16/1.05  fof(f1,axiom,(
% 2.16/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f40,plain,(
% 2.16/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f1])).
% 2.16/1.05  
% 2.16/1.05  fof(f8,axiom,(
% 2.16/1.05    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.16/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.05  
% 2.16/1.05  fof(f50,plain,(
% 2.16/1.05    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f8])).
% 2.16/1.05  
% 2.16/1.05  fof(f61,plain,(
% 2.16/1.05    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.05    inference(cnf_transformation,[],[f37])).
% 2.16/1.05  
% 2.16/1.05  fof(f73,plain,(
% 2.16/1.05    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.16/1.05    inference(equality_resolution,[],[f61])).
% 2.16/1.05  
% 2.16/1.05  fof(f44,plain,(
% 2.16/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.16/1.05    inference(cnf_transformation,[],[f34])).
% 2.16/1.05  
% 2.16/1.05  fof(f69,plain,(
% 2.16/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.16/1.05    inference(equality_resolution,[],[f44])).
% 2.16/1.05  
% 2.16/1.05  fof(f46,plain,(
% 2.16/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.16/1.05    inference(cnf_transformation,[],[f34])).
% 2.16/1.05  
% 2.16/1.05  cnf(c_21,plain,
% 2.16/1.05      ( v1_funct_2(X0,X1,X2)
% 2.16/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | k1_relset_1(X1,X2,X0) != X1
% 2.16/1.05      | k1_xboole_0 = X2 ),
% 2.16/1.05      inference(cnf_transformation,[],[f60]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_24,negated_conjecture,
% 2.16/1.05      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 2.16/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | ~ v1_funct_1(sK2) ),
% 2.16/1.05      inference(cnf_transformation,[],[f67]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_26,negated_conjecture,
% 2.16/1.05      ( v1_funct_1(sK2) ),
% 2.16/1.05      inference(cnf_transformation,[],[f65]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_154,plain,
% 2.16/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_24,c_26]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_155,negated_conjecture,
% 2.16/1.05      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 2.16/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
% 2.16/1.05      inference(renaming,[status(thm)],[c_154]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_482,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | k1_relset_1(X1,X2,X0) != X1
% 2.16/1.05      | k1_relat_1(sK2) != X1
% 2.16/1.05      | sK1 != X2
% 2.16/1.05      | sK2 != X0
% 2.16/1.05      | k1_xboole_0 = X2 ),
% 2.16/1.05      inference(resolution_lifted,[status(thm)],[c_21,c_155]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_483,plain,
% 2.16/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
% 2.16/1.05      | k1_xboole_0 = sK1 ),
% 2.16/1.05      inference(unflattening,[status(thm)],[c_482]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_16,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f56]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_491,plain,
% 2.16/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | k1_xboole_0 = sK1 ),
% 2.16/1.05      inference(forward_subsumption_resolution,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_483,c_16]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1036,plain,
% 2.16/1.05      ( k1_xboole_0 = sK1
% 2.16/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_25,negated_conjecture,
% 2.16/1.05      ( r1_tarski(k2_relat_1(sK2),sK1) ),
% 2.16/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_17,plain,
% 2.16/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.16/1.05      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.16/1.05      | ~ v1_relat_1(X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_27,negated_conjecture,
% 2.16/1.05      ( v1_relat_1(sK2) ),
% 2.16/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_392,plain,
% 2.16/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.05      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.16/1.05      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.16/1.05      | sK2 != X0 ),
% 2.16/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_393,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.16/1.05      | ~ r1_tarski(k2_relat_1(sK2),X1)
% 2.16/1.05      | ~ r1_tarski(k1_relat_1(sK2),X0) ),
% 2.16/1.05      inference(unflattening,[status(thm)],[c_392]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1157,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 2.16/1.05      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 2.16/1.05      | ~ r1_tarski(k1_relat_1(sK2),X0) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_393]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1237,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 2.16/1.05      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_1157]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_5,plain,
% 2.16/1.05      ( r1_tarski(X0,X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f68]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1238,plain,
% 2.16/1.05      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_5]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1259,plain,
% 2.16/1.05      ( k1_xboole_0 = sK1 ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_1036,c_25,c_491,c_1237,c_1238]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1041,plain,
% 2.16/1.05      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1264,plain,
% 2.16/1.05      ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_1259,c_1041]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_8,plain,
% 2.16/1.05      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f48]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_9,plain,
% 2.16/1.05      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f49]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_358,plain,
% 2.16/1.05      ( ~ r1_tarski(X0,X1)
% 2.16/1.05      | v1_xboole_0(X0)
% 2.16/1.05      | X0 != X2
% 2.16/1.05      | k1_xboole_0 != X1 ),
% 2.16/1.05      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_359,plain,
% 2.16/1.05      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 2.16/1.05      inference(unflattening,[status(thm)],[c_358]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1040,plain,
% 2.16/1.05      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.16/1.05      | v1_xboole_0(X0) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1860,plain,
% 2.16/1.05      ( v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1264,c_1040]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_3,plain,
% 2.16/1.05      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f43]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1048,plain,
% 2.16/1.05      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1870,plain,
% 2.16/1.05      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1860,c_1048]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_14,plain,
% 2.16/1.05      ( ~ v1_relat_1(X0)
% 2.16/1.05      | k2_relat_1(X0) != k1_xboole_0
% 2.16/1.05      | k1_relat_1(X0) = k1_xboole_0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f55]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_415,plain,
% 2.16/1.05      ( k2_relat_1(X0) != k1_xboole_0
% 2.16/1.05      | k1_relat_1(X0) = k1_xboole_0
% 2.16/1.05      | sK2 != X0 ),
% 2.16/1.05      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_416,plain,
% 2.16/1.05      ( k2_relat_1(sK2) != k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.16/1.05      inference(unflattening,[status(thm)],[c_415]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_563,plain,
% 2.16/1.05      ( k2_relat_1(sK2) != k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.16/1.05      inference(prop_impl,[status(thm)],[c_416]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1912,plain,
% 2.16/1.05      ( k1_relat_1(sK2) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_1870,c_563]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1928,plain,
% 2.16/1.05      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.16/1.05      inference(equality_resolution_simp,[status(thm)],[c_1912]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1038,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.16/1.05      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1915,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 2.16/1.05      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_1870,c_1038]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1931,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.16/1.05      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.16/1.05      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_1928,c_1915]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_7,plain,
% 2.16/1.05      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f47]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_0,plain,
% 2.16/1.05      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f40]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1513,plain,
% 2.16/1.05      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_10,plain,
% 2.16/1.05      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 2.16/1.05      inference(cnf_transformation,[],[f50]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1045,plain,
% 2.16/1.05      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1632,plain,
% 2.16/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_1513,c_1045]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2276,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.16/1.05      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_1931,c_1632]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2282,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.16/1.05      inference(forward_subsumption_resolution,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_2276,c_1632]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1042,plain,
% 2.16/1.05      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.16/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2287,plain,
% 2.16/1.05      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2) ),
% 2.16/1.05      inference(superposition,[status(thm)],[c_2282,c_1042]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2395,plain,
% 2.16/1.05      ( k1_relset_1(X0,X1,sK2) = k1_xboole_0 ),
% 2.16/1.05      inference(light_normalisation,[status(thm)],[c_2287,c_1928]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_2397,plain,
% 2.16/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_xboole_0 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_2395]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1437,plain,
% 2.16/1.05      ( ~ v1_xboole_0(k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1438,plain,
% 2.16/1.05      ( k1_xboole_0 = k2_relat_1(sK2)
% 2.16/1.05      | v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_1437]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1359,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 2.16/1.05      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 2.16/1.05      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_393]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1361,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
% 2.16/1.05      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_1359]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1363,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top
% 2.16/1.05      | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_1361]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_20,plain,
% 2.16/1.05      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.16/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.16/1.05      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.16/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_466,plain,
% 2.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.16/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.16/1.05      | k1_relat_1(sK2) != k1_xboole_0
% 2.16/1.05      | sK1 != X1
% 2.16/1.05      | sK2 != X0 ),
% 2.16/1.05      inference(resolution_lifted,[status(thm)],[c_20,c_155]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_467,plain,
% 2.16/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.16/1.05      | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 2.16/1.05      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.16/1.05      inference(unflattening,[status(thm)],[c_466]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_602,plain,
% 2.16/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.16/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.16/1.05      | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 2.16/1.05      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.16/1.05      inference(bin_hyper_res,[status(thm)],[c_467,c_563]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1035,plain,
% 2.16/1.05      ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 2.16/1.05      | k2_relat_1(sK2) != k1_xboole_0
% 2.16/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top
% 2.16/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1263,plain,
% 2.16/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
% 2.16/1.05      | k2_relat_1(sK2) != k1_xboole_0
% 2.16/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 2.16/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.16/1.05      inference(demodulation,[status(thm)],[c_1259,c_1035]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_6,plain,
% 2.16/1.05      ( r1_tarski(X0,X0) ),
% 2.16/1.05      inference(cnf_transformation,[],[f69]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_82,plain,
% 2.16/1.05      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_81,plain,
% 2.16/1.05      ( r1_tarski(X0,X0) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_83,plain,
% 2.16/1.05      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_81]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_4,plain,
% 2.16/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.16/1.05      inference(cnf_transformation,[],[f46]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_86,plain,
% 2.16/1.05      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.16/1.05      | k1_xboole_0 = k1_xboole_0 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_4]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_394,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.16/1.05      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_396,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 2.16/1.05      | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_394]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_660,plain,
% 2.16/1.05      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.16/1.05      theory(equality) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1253,plain,
% 2.16/1.05      ( ~ r1_tarski(X0,X1)
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),X2)
% 2.16/1.05      | X2 != X1
% 2.16/1.05      | k1_relat_1(sK2) != X0 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_660]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1254,plain,
% 2.16/1.05      ( X0 != X1
% 2.16/1.05      | k1_relat_1(sK2) != X2
% 2.16/1.05      | r1_tarski(X2,X1) != iProver_top
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),X0) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_1253]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1256,plain,
% 2.16/1.05      ( k1_relat_1(sK2) != k1_xboole_0
% 2.16/1.05      | k1_xboole_0 != k1_xboole_0
% 2.16/1.05      | r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top
% 2.16/1.05      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_1254]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1346,plain,
% 2.16/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top
% 2.16/1.05      | k2_relat_1(sK2) != k1_xboole_0
% 2.16/1.05      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0 ),
% 2.16/1.05      inference(global_propositional_subsumption,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_1263,c_82,c_83,c_86,c_396,c_416,c_1256,c_1264]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1347,plain,
% 2.16/1.05      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) != k1_xboole_0
% 2.16/1.05      | k2_relat_1(sK2) != k1_xboole_0
% 2.16/1.05      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) != iProver_top ),
% 2.16/1.05      inference(renaming,[status(thm)],[c_1346]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_657,plain,( X0 = X0 ),theory(equality) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1324,plain,
% 2.16/1.05      ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_657]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_658,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1230,plain,
% 2.16/1.05      ( k2_relat_1(sK2) != X0
% 2.16/1.05      | k2_relat_1(sK2) = k1_xboole_0
% 2.16/1.05      | k1_xboole_0 != X0 ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_658]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1323,plain,
% 2.16/1.05      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 2.16/1.05      | k2_relat_1(sK2) = k1_xboole_0
% 2.16/1.05      | k1_xboole_0 != k2_relat_1(sK2) ),
% 2.16/1.05      inference(instantiation,[status(thm)],[c_1230]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(c_1241,plain,
% 2.16/1.05      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 2.16/1.05      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 2.16/1.05  
% 2.16/1.05  cnf(contradiction,plain,
% 2.16/1.05      ( $false ),
% 2.16/1.05      inference(minisat,
% 2.16/1.05                [status(thm)],
% 2.16/1.05                [c_2397,c_1860,c_1438,c_1363,c_1347,c_1324,c_1323,c_1264,
% 2.16/1.05                 c_1241]) ).
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.05  
% 2.16/1.05  ------                               Statistics
% 2.16/1.05  
% 2.16/1.05  ------ General
% 2.16/1.05  
% 2.16/1.05  abstr_ref_over_cycles:                  0
% 2.16/1.05  abstr_ref_under_cycles:                 0
% 2.16/1.05  gc_basic_clause_elim:                   0
% 2.16/1.05  forced_gc_time:                         0
% 2.16/1.05  parsing_time:                           0.028
% 2.16/1.05  unif_index_cands_time:                  0.
% 2.16/1.05  unif_index_add_time:                    0.
% 2.16/1.05  orderings_time:                         0.
% 2.16/1.05  out_proof_time:                         0.008
% 2.16/1.05  total_time:                             0.194
% 2.16/1.05  num_of_symbols:                         49
% 2.16/1.05  num_of_terms:                           2093
% 2.16/1.05  
% 2.16/1.05  ------ Preprocessing
% 2.16/1.05  
% 2.16/1.05  num_of_splits:                          0
% 2.16/1.05  num_of_split_atoms:                     0
% 2.16/1.05  num_of_reused_defs:                     0
% 2.16/1.05  num_eq_ax_congr_red:                    11
% 2.16/1.05  num_of_sem_filtered_clauses:            2
% 2.16/1.05  num_of_subtypes:                        0
% 2.16/1.05  monotx_restored_types:                  0
% 2.16/1.05  sat_num_of_epr_types:                   0
% 2.16/1.05  sat_num_of_non_cyclic_types:            0
% 2.16/1.05  sat_guarded_non_collapsed_types:        0
% 2.16/1.05  num_pure_diseq_elim:                    0
% 2.16/1.05  simp_replaced_by:                       0
% 2.16/1.05  res_preprocessed:                       102
% 2.16/1.05  prep_upred:                             0
% 2.16/1.05  prep_unflattend:                        35
% 2.16/1.05  smt_new_axioms:                         0
% 2.16/1.05  pred_elim_cands:                        3
% 2.16/1.05  pred_elim:                              4
% 2.16/1.05  pred_elim_cl:                           8
% 2.16/1.05  pred_elim_cycles:                       6
% 2.16/1.05  merged_defs:                            14
% 2.16/1.05  merged_defs_ncl:                        0
% 2.16/1.05  bin_hyper_res:                          16
% 2.16/1.05  prep_cycles:                            4
% 2.16/1.05  pred_elim_time:                         0.007
% 2.16/1.05  splitting_time:                         0.
% 2.16/1.05  sem_filter_time:                        0.
% 2.16/1.05  monotx_time:                            0.001
% 2.16/1.05  subtype_inf_time:                       0.
% 2.16/1.05  
% 2.16/1.05  ------ Problem properties
% 2.16/1.05  
% 2.16/1.05  clauses:                                18
% 2.16/1.05  conjectures:                            1
% 2.16/1.05  epr:                                    5
% 2.16/1.05  horn:                                   18
% 2.16/1.05  ground:                                 6
% 2.16/1.05  unary:                                  5
% 2.16/1.05  binary:                                 8
% 2.16/1.05  lits:                                   39
% 2.16/1.05  lits_eq:                                15
% 2.16/1.05  fd_pure:                                0
% 2.16/1.05  fd_pseudo:                              0
% 2.16/1.05  fd_cond:                                1
% 2.16/1.05  fd_pseudo_cond:                         1
% 2.16/1.05  ac_symbols:                             0
% 2.16/1.05  
% 2.16/1.05  ------ Propositional Solver
% 2.16/1.05  
% 2.16/1.05  prop_solver_calls:                      27
% 2.16/1.05  prop_fast_solver_calls:                 562
% 2.16/1.05  smt_solver_calls:                       0
% 2.16/1.05  smt_fast_solver_calls:                  0
% 2.16/1.05  prop_num_of_clauses:                    771
% 2.16/1.05  prop_preprocess_simplified:             3319
% 2.16/1.05  prop_fo_subsumed:                       4
% 2.16/1.05  prop_solver_time:                       0.
% 2.16/1.05  smt_solver_time:                        0.
% 2.16/1.05  smt_fast_solver_time:                   0.
% 2.16/1.05  prop_fast_solver_time:                  0.
% 2.16/1.05  prop_unsat_core_time:                   0.
% 2.16/1.05  
% 2.16/1.05  ------ QBF
% 2.16/1.05  
% 2.16/1.05  qbf_q_res:                              0
% 2.16/1.05  qbf_num_tautologies:                    0
% 2.16/1.05  qbf_prep_cycles:                        0
% 2.16/1.05  
% 2.16/1.05  ------ BMC1
% 2.16/1.05  
% 2.16/1.05  bmc1_current_bound:                     -1
% 2.16/1.05  bmc1_last_solved_bound:                 -1
% 2.16/1.05  bmc1_unsat_core_size:                   -1
% 2.16/1.05  bmc1_unsat_core_parents_size:           -1
% 2.16/1.05  bmc1_merge_next_fun:                    0
% 2.16/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.05  
% 2.16/1.05  ------ Instantiation
% 2.16/1.05  
% 2.16/1.05  inst_num_of_clauses:                    239
% 2.16/1.05  inst_num_in_passive:                    114
% 2.16/1.05  inst_num_in_active:                     108
% 2.16/1.05  inst_num_in_unprocessed:                17
% 2.16/1.05  inst_num_of_loops:                      150
% 2.16/1.05  inst_num_of_learning_restarts:          0
% 2.16/1.05  inst_num_moves_active_passive:          39
% 2.16/1.05  inst_lit_activity:                      0
% 2.16/1.05  inst_lit_activity_moves:                0
% 2.16/1.05  inst_num_tautologies:                   0
% 2.16/1.05  inst_num_prop_implied:                  0
% 2.16/1.05  inst_num_existing_simplified:           0
% 2.16/1.05  inst_num_eq_res_simplified:             0
% 2.16/1.05  inst_num_child_elim:                    0
% 2.16/1.05  inst_num_of_dismatching_blockings:      48
% 2.16/1.05  inst_num_of_non_proper_insts:           236
% 2.16/1.05  inst_num_of_duplicates:                 0
% 2.16/1.05  inst_inst_num_from_inst_to_res:         0
% 2.16/1.05  inst_dismatching_checking_time:         0.
% 2.16/1.05  
% 2.16/1.05  ------ Resolution
% 2.16/1.05  
% 2.16/1.05  res_num_of_clauses:                     0
% 2.16/1.05  res_num_in_passive:                     0
% 2.16/1.05  res_num_in_active:                      0
% 2.16/1.05  res_num_of_loops:                       106
% 2.16/1.05  res_forward_subset_subsumed:            21
% 2.16/1.05  res_backward_subset_subsumed:           0
% 2.16/1.05  res_forward_subsumed:                   0
% 2.16/1.05  res_backward_subsumed:                  0
% 2.16/1.05  res_forward_subsumption_resolution:     1
% 2.16/1.05  res_backward_subsumption_resolution:    0
% 2.16/1.05  res_clause_to_clause_subsumption:       119
% 2.16/1.05  res_orphan_elimination:                 0
% 2.16/1.05  res_tautology_del:                      44
% 2.16/1.05  res_num_eq_res_simplified:              0
% 2.16/1.05  res_num_sel_changes:                    0
% 2.16/1.05  res_moves_from_active_to_pass:          0
% 2.16/1.05  
% 2.16/1.05  ------ Superposition
% 2.16/1.05  
% 2.16/1.05  sup_time_total:                         0.
% 2.16/1.05  sup_time_generating:                    0.
% 2.16/1.05  sup_time_sim_full:                      0.
% 2.16/1.05  sup_time_sim_immed:                     0.
% 2.16/1.05  
% 2.16/1.05  sup_num_of_clauses:                     30
% 2.16/1.05  sup_num_in_active:                      19
% 2.16/1.05  sup_num_in_passive:                     11
% 2.16/1.05  sup_num_of_loops:                       29
% 2.16/1.05  sup_fw_superposition:                   24
% 2.16/1.05  sup_bw_superposition:                   10
% 2.16/1.05  sup_immediate_simplified:               4
% 2.16/1.05  sup_given_eliminated:                   0
% 2.16/1.05  comparisons_done:                       0
% 2.16/1.05  comparisons_avoided:                    0
% 2.16/1.05  
% 2.16/1.05  ------ Simplifications
% 2.16/1.05  
% 2.16/1.05  
% 2.16/1.05  sim_fw_subset_subsumed:                 1
% 2.16/1.05  sim_bw_subset_subsumed:                 2
% 2.16/1.05  sim_fw_subsumed:                        1
% 2.16/1.05  sim_bw_subsumed:                        0
% 2.16/1.05  sim_fw_subsumption_res:                 1
% 2.16/1.05  sim_bw_subsumption_res:                 0
% 2.16/1.05  sim_tautology_del:                      1
% 2.16/1.05  sim_eq_tautology_del:                   1
% 2.16/1.05  sim_eq_res_simp:                        3
% 2.16/1.05  sim_fw_demodulated:                     0
% 2.16/1.05  sim_bw_demodulated:                     10
% 2.16/1.05  sim_light_normalised:                   1
% 2.16/1.05  sim_joinable_taut:                      0
% 2.16/1.05  sim_joinable_simp:                      0
% 2.16/1.05  sim_ac_normalised:                      0
% 2.16/1.05  sim_smt_subsumption:                    0
% 2.16/1.05  
%------------------------------------------------------------------------------
