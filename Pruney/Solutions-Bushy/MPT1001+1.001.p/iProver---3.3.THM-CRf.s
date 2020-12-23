%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1001+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:37 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 988 expanded)
%              Number of clauses        :   51 ( 297 expanded)
%              Number of leaves         :   12 ( 188 expanded)
%              Depth                    :   27
%              Number of atoms          :  277 (4028 expanded)
%              Number of equality atoms :  146 (1965 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
          & r2_hidden(X2,X0) )
     => ( k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ( k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0
        & r2_hidden(sK0(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) != k1_xboole_0
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) != k1_xboole_0
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) != k1_xboole_0
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X4] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X4)) != k1_xboole_0
            | ~ r2_hidden(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
          & r2_hidden(X3,X1) )
     => ( k8_relset_1(X0,X1,X2,k1_tarski(sK4)) = k1_xboole_0
        & r2_hidden(sK4,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X4] :
              ( k8_relset_1(X0,X1,X2,k1_tarski(X4)) != k1_xboole_0
              | ~ r2_hidden(X4,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK1,sK2,sK3) != sK2
        | ? [X3] :
            ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X3)) = k1_xboole_0
            & r2_hidden(X3,sK2) ) )
      & ( k2_relset_1(sK1,sK2,sK3) = sK2
        | ! [X4] :
            ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X4)) != k1_xboole_0
            | ~ r2_hidden(X4,sK2) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( k2_relset_1(sK1,sK2,sK3) != sK2
      | ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) = k1_xboole_0
        & r2_hidden(sK4,sK2) ) )
    & ( k2_relset_1(sK1,sK2,sK3) = sK2
      | ! [X4] :
          ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X4)) != k1_xboole_0
          | ~ r2_hidden(X4,sK2) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f31,f30])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X4] :
      ( k2_relset_1(sK1,sK2,sK3) = sK2
      | k8_relset_1(sK1,sK2,sK3,k1_tarski(X4)) != k1_xboole_0
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | r2_hidden(sK0(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_tarski(sK0(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1078,plain,
    ( k10_relat_1(X0,k1_tarski(sK0(X1,X0))) = k1_xboole_0
    | r1_tarski(X1,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1072,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1082,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1477,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1072,c_1082])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2067,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1477,c_1083])).

cnf(c_17,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2252,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_17])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1075,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2257,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_1075])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1085,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2321,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2257,c_1085])).

cnf(c_2434,plain,
    ( k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
    | k2_relat_1(sK3) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_2321])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1192,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2435,plain,
    ( ~ v1_relat_1(sK3)
    | k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
    | k2_relat_1(sK3) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2434])).

cnf(c_2437,plain,
    ( k2_relat_1(sK3) = sK2
    | k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2434,c_16,c_1192,c_2435])).

cnf(c_2438,plain,
    ( k10_relat_1(sK3,k1_tarski(sK0(sK2,sK3))) = k1_xboole_0
    | k2_relat_1(sK3) = sK2 ),
    inference(renaming,[status(thm)],[c_2437])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1081,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1930,plain,
    ( k8_relset_1(sK1,sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1072,c_1081])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1073,plain,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1657,plain,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(X0)) != k1_xboole_0
    | k2_relat_1(sK3) = sK2
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1477,c_1073])).

cnf(c_2163,plain,
    ( k10_relat_1(sK3,k1_tarski(X0)) != k1_xboole_0
    | k2_relat_1(sK3) = sK2
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1930,c_1657])).

cnf(c_2442,plain,
    ( k2_relat_1(sK3) = sK2
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2438,c_2163])).

cnf(c_1193,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_10,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1235,plain,
    ( r2_hidden(sK0(X0,sK3),X0)
    | r1_tarski(X0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1251,plain,
    ( r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_1253,plain,
    ( r2_hidden(sK0(sK2,sK3),sK2) = iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_2522,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2442,c_17,c_1193,c_1253,c_2321])).

cnf(c_13,negated_conjecture,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) = k1_xboole_0
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1659,plain,
    ( k8_relset_1(sK1,sK2,sK3,k1_tarski(sK4)) = k1_xboole_0
    | k2_relat_1(sK3) != sK2 ),
    inference(demodulation,[status(thm)],[c_1477,c_13])).

cnf(c_2162,plain,
    ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0
    | k2_relat_1(sK3) != sK2 ),
    inference(demodulation,[status(thm)],[c_1930,c_1659])).

cnf(c_2528,plain,
    ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_2522,c_2162])).

cnf(c_2536,plain,
    ( k10_relat_1(sK3,k1_tarski(sK4)) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2528])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1079,plain,
    ( k10_relat_1(X0,k1_tarski(X1)) != k1_xboole_0
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3096,plain,
    ( r2_hidden(sK4,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2536,c_1079])).

cnf(c_3097,plain,
    ( r2_hidden(sK4,sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3096,c_2522])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1074,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1658,plain,
    ( k2_relat_1(sK3) != sK2
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1477,c_1074])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3097,c_2522,c_1658,c_1193,c_17])).


%------------------------------------------------------------------------------
