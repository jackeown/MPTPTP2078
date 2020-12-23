%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:32 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 243 expanded)
%              Number of clauses        :   48 (  92 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  200 ( 595 expanded)
%              Number of equality atoms :  102 ( 284 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f28])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_185,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_186,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_212,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_186])).

cnf(c_213,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_263,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_213])).

cnf(c_392,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_133,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_134,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_14,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X1 != X0
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_134,c_14])).

cnf(c_149,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_197,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k1_xboole_0)
    | sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_149])).

cnf(c_198,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_415,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_198,c_6])).

cnf(c_416,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_415])).

cnf(c_422,plain,
    ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_392,c_11,c_416])).

cnf(c_264,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_213])).

cnf(c_284,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_266,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_470,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_262,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_213])).

cnf(c_471,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_474,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_535,plain,
    ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_284,c_470,c_474])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_396,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_940,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_535,c_396])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_394,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_956,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_940,c_394])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_176,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_177,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_444,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_177,c_416])).

cnf(c_445,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_444,c_6])).

cnf(c_732,plain,
    ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) = k10_relat_1(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_445])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_418,plain,
    ( k8_relset_1(k1_xboole_0,sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_416,c_15])).

cnf(c_845,plain,
    ( k10_relat_1(k1_xboole_0,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_732,c_418])).

cnf(c_962,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_956,c_845])).

cnf(c_963,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_962])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:42:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.61/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/0.94  
% 1.61/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.61/0.94  
% 1.61/0.94  ------  iProver source info
% 1.61/0.94  
% 1.61/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.61/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.61/0.94  git: non_committed_changes: false
% 1.61/0.94  git: last_make_outside_of_git: false
% 1.61/0.94  
% 1.61/0.94  ------ 
% 1.61/0.94  
% 1.61/0.94  ------ Input Options
% 1.61/0.94  
% 1.61/0.94  --out_options                           all
% 1.61/0.94  --tptp_safe_out                         true
% 1.61/0.94  --problem_path                          ""
% 1.61/0.94  --include_path                          ""
% 1.61/0.94  --clausifier                            res/vclausify_rel
% 1.61/0.94  --clausifier_options                    --mode clausify
% 1.61/0.94  --stdin                                 false
% 1.61/0.94  --stats_out                             all
% 1.61/0.94  
% 1.61/0.94  ------ General Options
% 1.61/0.94  
% 1.61/0.94  --fof                                   false
% 1.61/0.94  --time_out_real                         305.
% 1.61/0.94  --time_out_virtual                      -1.
% 1.61/0.94  --symbol_type_check                     false
% 1.61/0.94  --clausify_out                          false
% 1.61/0.94  --sig_cnt_out                           false
% 1.61/0.94  --trig_cnt_out                          false
% 1.61/0.94  --trig_cnt_out_tolerance                1.
% 1.61/0.94  --trig_cnt_out_sk_spl                   false
% 1.61/0.94  --abstr_cl_out                          false
% 1.61/0.94  
% 1.61/0.94  ------ Global Options
% 1.61/0.94  
% 1.61/0.94  --schedule                              default
% 1.61/0.94  --add_important_lit                     false
% 1.61/0.94  --prop_solver_per_cl                    1000
% 1.61/0.94  --min_unsat_core                        false
% 1.61/0.94  --soft_assumptions                      false
% 1.61/0.94  --soft_lemma_size                       3
% 1.61/0.94  --prop_impl_unit_size                   0
% 1.61/0.94  --prop_impl_unit                        []
% 1.61/0.94  --share_sel_clauses                     true
% 1.61/0.94  --reset_solvers                         false
% 1.61/0.94  --bc_imp_inh                            [conj_cone]
% 1.61/0.94  --conj_cone_tolerance                   3.
% 1.61/0.94  --extra_neg_conj                        none
% 1.61/0.94  --large_theory_mode                     true
% 1.61/0.94  --prolific_symb_bound                   200
% 1.61/0.94  --lt_threshold                          2000
% 1.61/0.94  --clause_weak_htbl                      true
% 1.61/0.94  --gc_record_bc_elim                     false
% 1.61/0.94  
% 1.61/0.94  ------ Preprocessing Options
% 1.61/0.94  
% 1.61/0.94  --preprocessing_flag                    true
% 1.61/0.94  --time_out_prep_mult                    0.1
% 1.61/0.94  --splitting_mode                        input
% 1.61/0.94  --splitting_grd                         true
% 1.61/0.94  --splitting_cvd                         false
% 1.61/0.94  --splitting_cvd_svl                     false
% 1.61/0.94  --splitting_nvd                         32
% 1.61/0.94  --sub_typing                            true
% 1.61/0.94  --prep_gs_sim                           true
% 1.61/0.94  --prep_unflatten                        true
% 1.61/0.94  --prep_res_sim                          true
% 1.61/0.94  --prep_upred                            true
% 1.61/0.94  --prep_sem_filter                       exhaustive
% 1.61/0.94  --prep_sem_filter_out                   false
% 1.61/0.94  --pred_elim                             true
% 1.61/0.94  --res_sim_input                         true
% 1.61/0.94  --eq_ax_congr_red                       true
% 1.61/0.94  --pure_diseq_elim                       true
% 1.61/0.94  --brand_transform                       false
% 1.61/0.94  --non_eq_to_eq                          false
% 1.61/0.94  --prep_def_merge                        true
% 1.61/0.94  --prep_def_merge_prop_impl              false
% 1.61/0.94  --prep_def_merge_mbd                    true
% 1.61/0.94  --prep_def_merge_tr_red                 false
% 1.61/0.94  --prep_def_merge_tr_cl                  false
% 1.61/0.94  --smt_preprocessing                     true
% 1.61/0.94  --smt_ac_axioms                         fast
% 1.61/0.94  --preprocessed_out                      false
% 1.61/0.94  --preprocessed_stats                    false
% 1.61/0.94  
% 1.61/0.94  ------ Abstraction refinement Options
% 1.61/0.94  
% 1.61/0.94  --abstr_ref                             []
% 1.61/0.94  --abstr_ref_prep                        false
% 1.61/0.94  --abstr_ref_until_sat                   false
% 1.61/0.94  --abstr_ref_sig_restrict                funpre
% 1.61/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.61/0.94  --abstr_ref_under                       []
% 1.61/0.94  
% 1.61/0.94  ------ SAT Options
% 1.61/0.94  
% 1.61/0.94  --sat_mode                              false
% 1.61/0.94  --sat_fm_restart_options                ""
% 1.61/0.94  --sat_gr_def                            false
% 1.61/0.94  --sat_epr_types                         true
% 1.61/0.94  --sat_non_cyclic_types                  false
% 1.61/0.94  --sat_finite_models                     false
% 1.61/0.94  --sat_fm_lemmas                         false
% 1.61/0.94  --sat_fm_prep                           false
% 1.61/0.94  --sat_fm_uc_incr                        true
% 1.61/0.94  --sat_out_model                         small
% 1.61/0.94  --sat_out_clauses                       false
% 1.61/0.94  
% 1.61/0.94  ------ QBF Options
% 1.61/0.94  
% 1.61/0.94  --qbf_mode                              false
% 1.61/0.94  --qbf_elim_univ                         false
% 1.61/0.94  --qbf_dom_inst                          none
% 1.61/0.94  --qbf_dom_pre_inst                      false
% 1.61/0.94  --qbf_sk_in                             false
% 1.61/0.94  --qbf_pred_elim                         true
% 1.61/0.94  --qbf_split                             512
% 1.61/0.94  
% 1.61/0.94  ------ BMC1 Options
% 1.61/0.94  
% 1.61/0.94  --bmc1_incremental                      false
% 1.61/0.94  --bmc1_axioms                           reachable_all
% 1.61/0.94  --bmc1_min_bound                        0
% 1.61/0.94  --bmc1_max_bound                        -1
% 1.61/0.94  --bmc1_max_bound_default                -1
% 1.61/0.94  --bmc1_symbol_reachability              true
% 1.61/0.94  --bmc1_property_lemmas                  false
% 1.61/0.94  --bmc1_k_induction                      false
% 1.61/0.94  --bmc1_non_equiv_states                 false
% 1.61/0.94  --bmc1_deadlock                         false
% 1.61/0.94  --bmc1_ucm                              false
% 1.61/0.94  --bmc1_add_unsat_core                   none
% 1.61/0.94  --bmc1_unsat_core_children              false
% 1.61/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.61/0.94  --bmc1_out_stat                         full
% 1.61/0.94  --bmc1_ground_init                      false
% 1.61/0.94  --bmc1_pre_inst_next_state              false
% 1.61/0.94  --bmc1_pre_inst_state                   false
% 1.61/0.94  --bmc1_pre_inst_reach_state             false
% 1.61/0.94  --bmc1_out_unsat_core                   false
% 1.61/0.94  --bmc1_aig_witness_out                  false
% 1.61/0.94  --bmc1_verbose                          false
% 1.61/0.94  --bmc1_dump_clauses_tptp                false
% 1.61/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.61/0.94  --bmc1_dump_file                        -
% 1.61/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.61/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.61/0.94  --bmc1_ucm_extend_mode                  1
% 1.61/0.94  --bmc1_ucm_init_mode                    2
% 1.61/0.94  --bmc1_ucm_cone_mode                    none
% 1.61/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.61/0.94  --bmc1_ucm_relax_model                  4
% 1.61/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.61/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.61/0.94  --bmc1_ucm_layered_model                none
% 1.61/0.94  --bmc1_ucm_max_lemma_size               10
% 1.61/0.94  
% 1.61/0.94  ------ AIG Options
% 1.61/0.94  
% 1.61/0.94  --aig_mode                              false
% 1.61/0.94  
% 1.61/0.94  ------ Instantiation Options
% 1.61/0.94  
% 1.61/0.94  --instantiation_flag                    true
% 1.61/0.94  --inst_sos_flag                         false
% 1.61/0.94  --inst_sos_phase                        true
% 1.61/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.61/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.61/0.94  --inst_lit_sel_side                     num_symb
% 1.61/0.94  --inst_solver_per_active                1400
% 1.61/0.94  --inst_solver_calls_frac                1.
% 1.61/0.94  --inst_passive_queue_type               priority_queues
% 1.61/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.61/0.94  --inst_passive_queues_freq              [25;2]
% 1.61/0.94  --inst_dismatching                      true
% 1.61/0.94  --inst_eager_unprocessed_to_passive     true
% 1.61/0.94  --inst_prop_sim_given                   true
% 1.61/0.94  --inst_prop_sim_new                     false
% 1.61/0.94  --inst_subs_new                         false
% 1.61/0.94  --inst_eq_res_simp                      false
% 1.61/0.94  --inst_subs_given                       false
% 1.61/0.94  --inst_orphan_elimination               true
% 1.61/0.94  --inst_learning_loop_flag               true
% 1.61/0.94  --inst_learning_start                   3000
% 1.61/0.94  --inst_learning_factor                  2
% 1.61/0.94  --inst_start_prop_sim_after_learn       3
% 1.61/0.94  --inst_sel_renew                        solver
% 1.61/0.94  --inst_lit_activity_flag                true
% 1.61/0.94  --inst_restr_to_given                   false
% 1.61/0.94  --inst_activity_threshold               500
% 1.61/0.94  --inst_out_proof                        true
% 1.61/0.94  
% 1.61/0.94  ------ Resolution Options
% 1.61/0.94  
% 1.61/0.94  --resolution_flag                       true
% 1.61/0.94  --res_lit_sel                           adaptive
% 1.61/0.94  --res_lit_sel_side                      none
% 1.61/0.94  --res_ordering                          kbo
% 1.61/0.94  --res_to_prop_solver                    active
% 1.61/0.94  --res_prop_simpl_new                    false
% 1.61/0.94  --res_prop_simpl_given                  true
% 1.61/0.94  --res_passive_queue_type                priority_queues
% 1.61/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.61/0.94  --res_passive_queues_freq               [15;5]
% 1.61/0.94  --res_forward_subs                      full
% 1.61/0.94  --res_backward_subs                     full
% 1.61/0.94  --res_forward_subs_resolution           true
% 1.61/0.94  --res_backward_subs_resolution          true
% 1.61/0.94  --res_orphan_elimination                true
% 1.61/0.94  --res_time_limit                        2.
% 1.61/0.94  --res_out_proof                         true
% 1.61/0.94  
% 1.61/0.94  ------ Superposition Options
% 1.61/0.94  
% 1.61/0.94  --superposition_flag                    true
% 1.61/0.94  --sup_passive_queue_type                priority_queues
% 1.61/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.61/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.61/0.94  --demod_completeness_check              fast
% 1.61/0.94  --demod_use_ground                      true
% 1.61/0.94  --sup_to_prop_solver                    passive
% 1.61/0.94  --sup_prop_simpl_new                    true
% 1.61/0.94  --sup_prop_simpl_given                  true
% 1.61/0.94  --sup_fun_splitting                     false
% 1.61/0.94  --sup_smt_interval                      50000
% 1.61/0.94  
% 1.61/0.94  ------ Superposition Simplification Setup
% 1.61/0.94  
% 1.61/0.94  --sup_indices_passive                   []
% 1.61/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.61/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.94  --sup_full_bw                           [BwDemod]
% 1.61/0.94  --sup_immed_triv                        [TrivRules]
% 1.61/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.61/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.94  --sup_immed_bw_main                     []
% 1.61/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.61/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/0.94  
% 1.61/0.94  ------ Combination Options
% 1.61/0.94  
% 1.61/0.94  --comb_res_mult                         3
% 1.61/0.94  --comb_sup_mult                         2
% 1.61/0.94  --comb_inst_mult                        10
% 1.61/0.94  
% 1.61/0.94  ------ Debug Options
% 1.61/0.94  
% 1.61/0.94  --dbg_backtrace                         false
% 1.61/0.94  --dbg_dump_prop_clauses                 false
% 1.61/0.94  --dbg_dump_prop_clauses_file            -
% 1.61/0.94  --dbg_out_stat                          false
% 1.61/0.94  ------ Parsing...
% 1.61/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.61/0.94  
% 1.61/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.61/0.94  
% 1.61/0.94  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.61/0.94  
% 1.61/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.61/0.94  ------ Proving...
% 1.61/0.94  ------ Problem Properties 
% 1.61/0.94  
% 1.61/0.94  
% 1.61/0.94  clauses                                 14
% 1.61/0.94  conjectures                             1
% 1.61/0.94  EPR                                     4
% 1.61/0.94  Horn                                    12
% 1.61/0.94  unary                                   7
% 1.61/0.94  binary                                  5
% 1.61/0.94  lits                                    23
% 1.61/0.94  lits eq                                 14
% 1.61/0.94  fd_pure                                 0
% 1.61/0.94  fd_pseudo                               0
% 1.61/0.94  fd_cond                                 1
% 1.61/0.94  fd_pseudo_cond                          1
% 1.61/0.94  AC symbols                              0
% 1.61/0.94  
% 1.61/0.94  ------ Schedule dynamic 5 is on 
% 1.61/0.94  
% 1.61/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.61/0.94  
% 1.61/0.94  
% 1.61/0.94  ------ 
% 1.61/0.94  Current options:
% 1.61/0.94  ------ 
% 1.61/0.94  
% 1.61/0.94  ------ Input Options
% 1.61/0.94  
% 1.61/0.94  --out_options                           all
% 1.61/0.94  --tptp_safe_out                         true
% 1.61/0.94  --problem_path                          ""
% 1.61/0.94  --include_path                          ""
% 1.61/0.94  --clausifier                            res/vclausify_rel
% 1.61/0.94  --clausifier_options                    --mode clausify
% 1.61/0.94  --stdin                                 false
% 1.61/0.94  --stats_out                             all
% 1.61/0.94  
% 1.61/0.94  ------ General Options
% 1.61/0.94  
% 1.61/0.94  --fof                                   false
% 1.61/0.94  --time_out_real                         305.
% 1.61/0.94  --time_out_virtual                      -1.
% 1.61/0.94  --symbol_type_check                     false
% 1.61/0.94  --clausify_out                          false
% 1.61/0.94  --sig_cnt_out                           false
% 1.61/0.94  --trig_cnt_out                          false
% 1.61/0.94  --trig_cnt_out_tolerance                1.
% 1.61/0.94  --trig_cnt_out_sk_spl                   false
% 1.61/0.94  --abstr_cl_out                          false
% 1.61/0.94  
% 1.61/0.94  ------ Global Options
% 1.61/0.94  
% 1.61/0.94  --schedule                              default
% 1.61/0.94  --add_important_lit                     false
% 1.61/0.94  --prop_solver_per_cl                    1000
% 1.61/0.94  --min_unsat_core                        false
% 1.61/0.94  --soft_assumptions                      false
% 1.61/0.94  --soft_lemma_size                       3
% 1.61/0.94  --prop_impl_unit_size                   0
% 1.61/0.94  --prop_impl_unit                        []
% 1.61/0.94  --share_sel_clauses                     true
% 1.61/0.94  --reset_solvers                         false
% 1.61/0.94  --bc_imp_inh                            [conj_cone]
% 1.61/0.94  --conj_cone_tolerance                   3.
% 1.61/0.94  --extra_neg_conj                        none
% 1.61/0.94  --large_theory_mode                     true
% 1.61/0.94  --prolific_symb_bound                   200
% 1.61/0.94  --lt_threshold                          2000
% 1.61/0.94  --clause_weak_htbl                      true
% 1.61/0.94  --gc_record_bc_elim                     false
% 1.61/0.94  
% 1.61/0.94  ------ Preprocessing Options
% 1.61/0.94  
% 1.61/0.94  --preprocessing_flag                    true
% 1.61/0.94  --time_out_prep_mult                    0.1
% 1.61/0.94  --splitting_mode                        input
% 1.61/0.94  --splitting_grd                         true
% 1.61/0.94  --splitting_cvd                         false
% 1.61/0.94  --splitting_cvd_svl                     false
% 1.61/0.94  --splitting_nvd                         32
% 1.61/0.94  --sub_typing                            true
% 1.61/0.94  --prep_gs_sim                           true
% 1.61/0.94  --prep_unflatten                        true
% 1.61/0.94  --prep_res_sim                          true
% 1.61/0.94  --prep_upred                            true
% 1.61/0.94  --prep_sem_filter                       exhaustive
% 1.61/0.94  --prep_sem_filter_out                   false
% 1.61/0.94  --pred_elim                             true
% 1.61/0.94  --res_sim_input                         true
% 1.61/0.94  --eq_ax_congr_red                       true
% 1.61/0.94  --pure_diseq_elim                       true
% 1.61/0.94  --brand_transform                       false
% 1.61/0.94  --non_eq_to_eq                          false
% 1.61/0.94  --prep_def_merge                        true
% 1.61/0.94  --prep_def_merge_prop_impl              false
% 1.61/0.94  --prep_def_merge_mbd                    true
% 1.61/0.94  --prep_def_merge_tr_red                 false
% 1.61/0.94  --prep_def_merge_tr_cl                  false
% 1.61/0.94  --smt_preprocessing                     true
% 1.61/0.94  --smt_ac_axioms                         fast
% 1.61/0.94  --preprocessed_out                      false
% 1.61/0.94  --preprocessed_stats                    false
% 1.61/0.94  
% 1.61/0.94  ------ Abstraction refinement Options
% 1.61/0.94  
% 1.61/0.94  --abstr_ref                             []
% 1.61/0.94  --abstr_ref_prep                        false
% 1.61/0.94  --abstr_ref_until_sat                   false
% 1.61/0.94  --abstr_ref_sig_restrict                funpre
% 1.61/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.61/0.94  --abstr_ref_under                       []
% 1.61/0.94  
% 1.61/0.94  ------ SAT Options
% 1.61/0.94  
% 1.61/0.94  --sat_mode                              false
% 1.61/0.94  --sat_fm_restart_options                ""
% 1.61/0.94  --sat_gr_def                            false
% 1.61/0.94  --sat_epr_types                         true
% 1.61/0.94  --sat_non_cyclic_types                  false
% 1.61/0.94  --sat_finite_models                     false
% 1.61/0.94  --sat_fm_lemmas                         false
% 1.61/0.94  --sat_fm_prep                           false
% 1.61/0.94  --sat_fm_uc_incr                        true
% 1.61/0.94  --sat_out_model                         small
% 1.61/0.94  --sat_out_clauses                       false
% 1.61/0.94  
% 1.61/0.94  ------ QBF Options
% 1.61/0.94  
% 1.61/0.94  --qbf_mode                              false
% 1.61/0.94  --qbf_elim_univ                         false
% 1.61/0.94  --qbf_dom_inst                          none
% 1.61/0.94  --qbf_dom_pre_inst                      false
% 1.61/0.94  --qbf_sk_in                             false
% 1.61/0.94  --qbf_pred_elim                         true
% 1.61/0.94  --qbf_split                             512
% 1.61/0.94  
% 1.61/0.94  ------ BMC1 Options
% 1.61/0.94  
% 1.61/0.94  --bmc1_incremental                      false
% 1.61/0.94  --bmc1_axioms                           reachable_all
% 1.61/0.94  --bmc1_min_bound                        0
% 1.61/0.94  --bmc1_max_bound                        -1
% 1.61/0.94  --bmc1_max_bound_default                -1
% 1.61/0.94  --bmc1_symbol_reachability              true
% 1.61/0.94  --bmc1_property_lemmas                  false
% 1.61/0.94  --bmc1_k_induction                      false
% 1.61/0.94  --bmc1_non_equiv_states                 false
% 1.61/0.94  --bmc1_deadlock                         false
% 1.61/0.94  --bmc1_ucm                              false
% 1.61/0.94  --bmc1_add_unsat_core                   none
% 1.61/0.94  --bmc1_unsat_core_children              false
% 1.61/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.61/0.94  --bmc1_out_stat                         full
% 1.61/0.94  --bmc1_ground_init                      false
% 1.61/0.94  --bmc1_pre_inst_next_state              false
% 1.61/0.94  --bmc1_pre_inst_state                   false
% 1.61/0.94  --bmc1_pre_inst_reach_state             false
% 1.61/0.94  --bmc1_out_unsat_core                   false
% 1.61/0.94  --bmc1_aig_witness_out                  false
% 1.61/0.94  --bmc1_verbose                          false
% 1.61/0.94  --bmc1_dump_clauses_tptp                false
% 1.61/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.61/0.94  --bmc1_dump_file                        -
% 1.61/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.61/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.61/0.94  --bmc1_ucm_extend_mode                  1
% 1.61/0.94  --bmc1_ucm_init_mode                    2
% 1.61/0.94  --bmc1_ucm_cone_mode                    none
% 1.61/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.61/0.94  --bmc1_ucm_relax_model                  4
% 1.61/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.61/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.61/0.94  --bmc1_ucm_layered_model                none
% 1.61/0.94  --bmc1_ucm_max_lemma_size               10
% 1.61/0.94  
% 1.61/0.94  ------ AIG Options
% 1.61/0.94  
% 1.61/0.94  --aig_mode                              false
% 1.61/0.94  
% 1.61/0.94  ------ Instantiation Options
% 1.61/0.94  
% 1.61/0.94  --instantiation_flag                    true
% 1.61/0.94  --inst_sos_flag                         false
% 1.61/0.94  --inst_sos_phase                        true
% 1.61/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.61/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.61/0.94  --inst_lit_sel_side                     none
% 1.61/0.94  --inst_solver_per_active                1400
% 1.61/0.94  --inst_solver_calls_frac                1.
% 1.61/0.94  --inst_passive_queue_type               priority_queues
% 1.61/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.61/0.94  --inst_passive_queues_freq              [25;2]
% 1.61/0.94  --inst_dismatching                      true
% 1.61/0.94  --inst_eager_unprocessed_to_passive     true
% 1.61/0.94  --inst_prop_sim_given                   true
% 1.61/0.94  --inst_prop_sim_new                     false
% 1.61/0.94  --inst_subs_new                         false
% 1.61/0.94  --inst_eq_res_simp                      false
% 1.61/0.94  --inst_subs_given                       false
% 1.61/0.94  --inst_orphan_elimination               true
% 1.61/0.94  --inst_learning_loop_flag               true
% 1.61/0.94  --inst_learning_start                   3000
% 1.61/0.94  --inst_learning_factor                  2
% 1.61/0.94  --inst_start_prop_sim_after_learn       3
% 1.61/0.94  --inst_sel_renew                        solver
% 1.61/0.94  --inst_lit_activity_flag                true
% 1.61/0.94  --inst_restr_to_given                   false
% 1.61/0.94  --inst_activity_threshold               500
% 1.61/0.94  --inst_out_proof                        true
% 1.61/0.94  
% 1.61/0.94  ------ Resolution Options
% 1.61/0.94  
% 1.61/0.94  --resolution_flag                       false
% 1.61/0.94  --res_lit_sel                           adaptive
% 1.61/0.94  --res_lit_sel_side                      none
% 1.61/0.94  --res_ordering                          kbo
% 1.61/0.94  --res_to_prop_solver                    active
% 1.61/0.94  --res_prop_simpl_new                    false
% 1.61/0.94  --res_prop_simpl_given                  true
% 1.61/0.94  --res_passive_queue_type                priority_queues
% 1.61/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.61/0.94  --res_passive_queues_freq               [15;5]
% 1.61/0.94  --res_forward_subs                      full
% 1.61/0.94  --res_backward_subs                     full
% 1.61/0.94  --res_forward_subs_resolution           true
% 1.61/0.94  --res_backward_subs_resolution          true
% 1.61/0.94  --res_orphan_elimination                true
% 1.61/0.94  --res_time_limit                        2.
% 1.61/0.94  --res_out_proof                         true
% 1.61/0.94  
% 1.61/0.94  ------ Superposition Options
% 1.61/0.94  
% 1.61/0.94  --superposition_flag                    true
% 1.61/0.94  --sup_passive_queue_type                priority_queues
% 1.61/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.61/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.61/0.94  --demod_completeness_check              fast
% 1.61/0.94  --demod_use_ground                      true
% 1.61/0.94  --sup_to_prop_solver                    passive
% 1.61/0.94  --sup_prop_simpl_new                    true
% 1.61/0.94  --sup_prop_simpl_given                  true
% 1.61/0.94  --sup_fun_splitting                     false
% 1.61/0.94  --sup_smt_interval                      50000
% 1.61/0.94  
% 1.61/0.94  ------ Superposition Simplification Setup
% 1.61/0.94  
% 1.61/0.94  --sup_indices_passive                   []
% 1.61/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.61/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.94  --sup_full_bw                           [BwDemod]
% 1.61/0.94  --sup_immed_triv                        [TrivRules]
% 1.61/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.61/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.94  --sup_immed_bw_main                     []
% 1.61/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.61/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/0.94  
% 1.61/0.94  ------ Combination Options
% 1.61/0.94  
% 1.61/0.94  --comb_res_mult                         3
% 1.61/0.94  --comb_sup_mult                         2
% 1.61/0.94  --comb_inst_mult                        10
% 1.61/0.94  
% 1.61/0.94  ------ Debug Options
% 1.61/0.94  
% 1.61/0.94  --dbg_backtrace                         false
% 1.61/0.94  --dbg_dump_prop_clauses                 false
% 1.61/0.94  --dbg_dump_prop_clauses_file            -
% 1.61/0.94  --dbg_out_stat                          false
% 1.61/0.94  
% 1.61/0.94  
% 1.61/0.94  
% 1.61/0.94  
% 1.61/0.94  ------ Proving...
% 1.61/0.94  
% 1.61/0.94  
% 1.61/0.94  % SZS status Theorem for theBenchmark.p
% 1.61/0.94  
% 1.61/0.94   Resolution empty clause
% 1.61/0.94  
% 1.61/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 1.61/0.94  
% 1.61/0.94  fof(f6,axiom,(
% 1.61/0.94    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f17,plain,(
% 1.61/0.94    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.61/0.94    inference(ennf_transformation,[],[f6])).
% 1.61/0.94  
% 1.61/0.94  fof(f39,plain,(
% 1.61/0.94    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.61/0.94    inference(cnf_transformation,[],[f17])).
% 1.61/0.94  
% 1.61/0.94  fof(f8,axiom,(
% 1.61/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f18,plain,(
% 1.61/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.94    inference(ennf_transformation,[],[f8])).
% 1.61/0.94  
% 1.61/0.94  fof(f42,plain,(
% 1.61/0.94    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.94    inference(cnf_transformation,[],[f18])).
% 1.61/0.94  
% 1.61/0.94  fof(f11,conjecture,(
% 1.61/0.94    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f12,negated_conjecture,(
% 1.61/0.94    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.61/0.94    inference(negated_conjecture,[],[f11])).
% 1.61/0.94  
% 1.61/0.94  fof(f13,plain,(
% 1.61/0.94    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.61/0.94    inference(pure_predicate_removal,[],[f12])).
% 1.61/0.94  
% 1.61/0.94  fof(f14,plain,(
% 1.61/0.94    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.61/0.94    inference(pure_predicate_removal,[],[f13])).
% 1.61/0.94  
% 1.61/0.94  fof(f21,plain,(
% 1.61/0.94    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 1.61/0.94    inference(ennf_transformation,[],[f14])).
% 1.61/0.94  
% 1.61/0.94  fof(f28,plain,(
% 1.61/0.94    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))))),
% 1.61/0.94    introduced(choice_axiom,[])).
% 1.61/0.94  
% 1.61/0.94  fof(f29,plain,(
% 1.61/0.94    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.61/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f28])).
% 1.61/0.94  
% 1.61/0.94  fof(f45,plain,(
% 1.61/0.94    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.61/0.94    inference(cnf_transformation,[],[f29])).
% 1.61/0.94  
% 1.61/0.94  fof(f7,axiom,(
% 1.61/0.94    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f40,plain,(
% 1.61/0.94    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.61/0.94    inference(cnf_transformation,[],[f7])).
% 1.61/0.94  
% 1.61/0.94  fof(f1,axiom,(
% 1.61/0.94    v1_xboole_0(k1_xboole_0)),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f30,plain,(
% 1.61/0.94    v1_xboole_0(k1_xboole_0)),
% 1.61/0.94    inference(cnf_transformation,[],[f1])).
% 1.61/0.94  
% 1.61/0.94  fof(f5,axiom,(
% 1.61/0.94    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f16,plain,(
% 1.61/0.94    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.61/0.94    inference(ennf_transformation,[],[f5])).
% 1.61/0.94  
% 1.61/0.94  fof(f38,plain,(
% 1.61/0.94    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.61/0.94    inference(cnf_transformation,[],[f16])).
% 1.61/0.94  
% 1.61/0.94  fof(f10,axiom,(
% 1.61/0.94    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f15,plain,(
% 1.61/0.94    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.61/0.94    inference(pure_predicate_removal,[],[f10])).
% 1.61/0.94  
% 1.61/0.94  fof(f20,plain,(
% 1.61/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.61/0.94    inference(ennf_transformation,[],[f15])).
% 1.61/0.94  
% 1.61/0.94  fof(f26,plain,(
% 1.61/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.61/0.94    introduced(choice_axiom,[])).
% 1.61/0.94  
% 1.61/0.94  fof(f27,plain,(
% 1.61/0.94    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.61/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).
% 1.61/0.94  
% 1.61/0.94  fof(f44,plain,(
% 1.61/0.94    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.61/0.94    inference(cnf_transformation,[],[f27])).
% 1.61/0.94  
% 1.61/0.94  fof(f4,axiom,(
% 1.61/0.94    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f24,plain,(
% 1.61/0.94    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.61/0.94    inference(nnf_transformation,[],[f4])).
% 1.61/0.94  
% 1.61/0.94  fof(f25,plain,(
% 1.61/0.94    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.61/0.94    inference(flattening,[],[f24])).
% 1.61/0.94  
% 1.61/0.94  fof(f36,plain,(
% 1.61/0.94    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.61/0.94    inference(cnf_transformation,[],[f25])).
% 1.61/0.94  
% 1.61/0.94  fof(f50,plain,(
% 1.61/0.94    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.61/0.94    inference(equality_resolution,[],[f36])).
% 1.61/0.94  
% 1.61/0.94  fof(f2,axiom,(
% 1.61/0.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f22,plain,(
% 1.61/0.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.94    inference(nnf_transformation,[],[f2])).
% 1.61/0.94  
% 1.61/0.94  fof(f23,plain,(
% 1.61/0.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.94    inference(flattening,[],[f22])).
% 1.61/0.94  
% 1.61/0.94  fof(f33,plain,(
% 1.61/0.94    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.61/0.94    inference(cnf_transformation,[],[f23])).
% 1.61/0.94  
% 1.61/0.94  fof(f3,axiom,(
% 1.61/0.94    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f34,plain,(
% 1.61/0.94    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.61/0.94    inference(cnf_transformation,[],[f3])).
% 1.61/0.94  
% 1.61/0.94  fof(f9,axiom,(
% 1.61/0.94    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.61/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.94  
% 1.61/0.94  fof(f19,plain,(
% 1.61/0.94    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.94    inference(ennf_transformation,[],[f9])).
% 1.61/0.94  
% 1.61/0.94  fof(f43,plain,(
% 1.61/0.94    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.94    inference(cnf_transformation,[],[f19])).
% 1.61/0.94  
% 1.61/0.94  fof(f46,plain,(
% 1.61/0.94    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2)),
% 1.61/0.94    inference(cnf_transformation,[],[f29])).
% 1.61/0.94  
% 1.61/0.94  cnf(c_9,plain,
% 1.61/0.94      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 1.61/0.94      inference(cnf_transformation,[],[f39]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_12,plain,
% 1.61/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.61/0.94      inference(cnf_transformation,[],[f42]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_16,negated_conjecture,
% 1.61/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
% 1.61/0.94      inference(cnf_transformation,[],[f45]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_185,plain,
% 1.61/0.94      ( v1_relat_1(X0)
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
% 1.61/0.94      | sK3 != X0 ),
% 1.61/0.94      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_186,plain,
% 1.61/0.94      ( v1_relat_1(sK3)
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
% 1.61/0.94      inference(unflattening,[status(thm)],[c_185]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_212,plain,
% 1.61/0.94      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
% 1.61/0.94      | sK3 != X0 ),
% 1.61/0.94      inference(resolution_lifted,[status(thm)],[c_9,c_186]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_213,plain,
% 1.61/0.94      ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3))
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
% 1.61/0.94      inference(unflattening,[status(thm)],[c_212]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_263,plain,
% 1.61/0.94      ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) | ~ sP1_iProver_split ),
% 1.61/0.94      inference(splitting,
% 1.61/0.94                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.61/0.94                [c_213]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_392,plain,
% 1.61/0.94      ( r1_tarski(k10_relat_1(sK3,X0),k1_relat_1(sK3)) = iProver_top
% 1.61/0.94      | sP1_iProver_split != iProver_top ),
% 1.61/0.94      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_11,plain,
% 1.61/0.94      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.61/0.94      inference(cnf_transformation,[],[f40]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_0,plain,
% 1.61/0.94      ( v1_xboole_0(k1_xboole_0) ),
% 1.61/0.94      inference(cnf_transformation,[],[f30]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_8,plain,
% 1.61/0.94      ( ~ r2_hidden(X0,X1)
% 1.61/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.61/0.94      | ~ v1_xboole_0(X2) ),
% 1.61/0.94      inference(cnf_transformation,[],[f38]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_133,plain,
% 1.61/0.94      ( ~ r2_hidden(X0,X1)
% 1.61/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.61/0.94      | k1_xboole_0 != X2 ),
% 1.61/0.94      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_134,plain,
% 1.61/0.94      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 1.61/0.94      inference(unflattening,[status(thm)],[c_133]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_14,plain,
% 1.61/0.94      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.61/0.94      inference(cnf_transformation,[],[f44]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_148,plain,
% 1.61/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 1.61/0.94      | X1 != X0
% 1.61/0.94      | sK0(X1) != X2
% 1.61/0.94      | k1_xboole_0 = X1 ),
% 1.61/0.94      inference(resolution_lifted,[status(thm)],[c_134,c_14]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_149,plain,
% 1.61/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 1.61/0.94      inference(unflattening,[status(thm)],[c_148]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_197,plain,
% 1.61/0.94      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k1_xboole_0)
% 1.61/0.94      | sK3 != X0
% 1.61/0.94      | k1_xboole_0 = X0 ),
% 1.61/0.94      inference(resolution_lifted,[status(thm)],[c_16,c_149]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_198,plain,
% 1.61/0.94      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k1_xboole_0)
% 1.61/0.94      | k1_xboole_0 = sK3 ),
% 1.61/0.94      inference(unflattening,[status(thm)],[c_197]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_6,plain,
% 1.61/0.94      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.61/0.94      inference(cnf_transformation,[],[f50]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_415,plain,
% 1.61/0.94      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 1.61/0.94      | sK3 = k1_xboole_0 ),
% 1.61/0.94      inference(demodulation,[status(thm)],[c_198,c_6]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_416,plain,
% 1.61/0.94      ( sK3 = k1_xboole_0 ),
% 1.61/0.94      inference(equality_resolution_simp,[status(thm)],[c_415]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_422,plain,
% 1.61/0.94      ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 1.61/0.94      | sP1_iProver_split != iProver_top ),
% 1.61/0.94      inference(light_normalisation,[status(thm)],[c_392,c_11,c_416]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_264,plain,
% 1.61/0.94      ( sP1_iProver_split | sP0_iProver_split ),
% 1.61/0.94      inference(splitting,
% 1.61/0.94                [splitting(split),new_symbols(definition,[])],
% 1.61/0.94                [c_213]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_284,plain,
% 1.61/0.94      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.61/0.94      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_266,plain,( X0 = X0 ),theory(equality) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_470,plain,
% 1.61/0.94      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
% 1.61/0.94      inference(instantiation,[status(thm)],[c_266]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_262,plain,
% 1.61/0.94      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
% 1.61/0.94      | ~ sP0_iProver_split ),
% 1.61/0.94      inference(splitting,
% 1.61/0.94                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.61/0.94                [c_213]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_471,plain,
% 1.61/0.94      ( ~ sP0_iProver_split
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
% 1.61/0.94      inference(instantiation,[status(thm)],[c_262]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_474,plain,
% 1.61/0.94      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
% 1.61/0.94      | sP0_iProver_split != iProver_top ),
% 1.61/0.94      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_535,plain,
% 1.61/0.94      ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 1.61/0.94      inference(global_propositional_subsumption,
% 1.61/0.94                [status(thm)],
% 1.61/0.94                [c_422,c_284,c_470,c_474]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_1,plain,
% 1.61/0.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.61/0.94      inference(cnf_transformation,[],[f33]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_396,plain,
% 1.61/0.94      ( X0 = X1
% 1.61/0.94      | r1_tarski(X0,X1) != iProver_top
% 1.61/0.94      | r1_tarski(X1,X0) != iProver_top ),
% 1.61/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_940,plain,
% 1.61/0.94      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 1.61/0.94      | r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)) != iProver_top ),
% 1.61/0.94      inference(superposition,[status(thm)],[c_535,c_396]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_4,plain,
% 1.61/0.94      ( r1_tarski(k1_xboole_0,X0) ),
% 1.61/0.94      inference(cnf_transformation,[],[f34]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_394,plain,
% 1.61/0.94      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.61/0.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_956,plain,
% 1.61/0.94      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.61/0.94      inference(forward_subsumption_resolution,[status(thm)],[c_940,c_394]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_13,plain,
% 1.61/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.61/0.94      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.61/0.94      inference(cnf_transformation,[],[f43]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_176,plain,
% 1.61/0.94      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))
% 1.61/0.94      | sK3 != X2 ),
% 1.61/0.94      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_177,plain,
% 1.61/0.94      ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
% 1.61/0.94      inference(unflattening,[status(thm)],[c_176]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_444,plain,
% 1.61/0.94      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2)
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)) ),
% 1.61/0.94      inference(light_normalisation,[status(thm)],[c_177,c_416]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_445,plain,
% 1.61/0.94      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2)
% 1.61/0.94      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k1_xboole_0) ),
% 1.61/0.94      inference(demodulation,[status(thm)],[c_444,c_6]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_732,plain,
% 1.61/0.94      ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) = k10_relat_1(k1_xboole_0,X1) ),
% 1.61/0.94      inference(superposition,[status(thm)],[c_6,c_445]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_15,negated_conjecture,
% 1.61/0.94      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK3,sK2) ),
% 1.61/0.94      inference(cnf_transformation,[],[f46]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_418,plain,
% 1.61/0.94      ( k8_relset_1(k1_xboole_0,sK1,k1_xboole_0,sK2) != k1_xboole_0 ),
% 1.61/0.94      inference(demodulation,[status(thm)],[c_416,c_15]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_845,plain,
% 1.61/0.94      ( k10_relat_1(k1_xboole_0,sK2) != k1_xboole_0 ),
% 1.61/0.94      inference(demodulation,[status(thm)],[c_732,c_418]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_962,plain,
% 1.61/0.94      ( k1_xboole_0 != k1_xboole_0 ),
% 1.61/0.94      inference(demodulation,[status(thm)],[c_956,c_845]) ).
% 1.61/0.94  
% 1.61/0.94  cnf(c_963,plain,
% 1.61/0.94      ( $false ),
% 1.61/0.94      inference(equality_resolution_simp,[status(thm)],[c_962]) ).
% 1.61/0.94  
% 1.61/0.94  
% 1.61/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 1.61/0.94  
% 1.61/0.94  ------                               Statistics
% 1.61/0.94  
% 1.61/0.94  ------ General
% 1.61/0.94  
% 1.61/0.94  abstr_ref_over_cycles:                  0
% 1.61/0.94  abstr_ref_under_cycles:                 0
% 1.61/0.94  gc_basic_clause_elim:                   0
% 1.61/0.94  forced_gc_time:                         0
% 1.61/0.94  parsing_time:                           0.01
% 1.61/0.94  unif_index_cands_time:                  0.
% 1.61/0.94  unif_index_add_time:                    0.
% 1.61/0.94  orderings_time:                         0.
% 1.61/0.94  out_proof_time:                         0.008
% 1.61/0.94  total_time:                             0.141
% 1.61/0.94  num_of_symbols:                         49
% 1.61/0.94  num_of_terms:                           1010
% 1.61/0.94  
% 1.61/0.94  ------ Preprocessing
% 1.61/0.94  
% 1.61/0.94  num_of_splits:                          2
% 1.61/0.94  num_of_split_atoms:                     2
% 1.61/0.94  num_of_reused_defs:                     0
% 1.61/0.94  num_eq_ax_congr_red:                    7
% 1.61/0.94  num_of_sem_filtered_clauses:            1
% 1.61/0.94  num_of_subtypes:                        0
% 1.61/0.94  monotx_restored_types:                  0
% 1.61/0.94  sat_num_of_epr_types:                   0
% 1.61/0.94  sat_num_of_non_cyclic_types:            0
% 1.61/0.94  sat_guarded_non_collapsed_types:        0
% 1.61/0.94  num_pure_diseq_elim:                    0
% 1.61/0.94  simp_replaced_by:                       0
% 1.61/0.94  res_preprocessed:                       75
% 1.61/0.94  prep_upred:                             0
% 1.61/0.94  prep_unflattend:                        7
% 1.61/0.94  smt_new_axioms:                         0
% 1.61/0.94  pred_elim_cands:                        1
% 1.61/0.94  pred_elim:                              4
% 1.61/0.94  pred_elim_cl:                           4
% 1.61/0.94  pred_elim_cycles:                       7
% 1.61/0.94  merged_defs:                            0
% 1.61/0.94  merged_defs_ncl:                        0
% 1.61/0.94  bin_hyper_res:                          0
% 1.61/0.94  prep_cycles:                            4
% 1.61/0.94  pred_elim_time:                         0.002
% 1.61/0.94  splitting_time:                         0.
% 1.61/0.94  sem_filter_time:                        0.
% 1.61/0.94  monotx_time:                            0.013
% 1.61/0.94  subtype_inf_time:                       0.
% 1.61/0.94  
% 1.61/0.94  ------ Problem properties
% 1.61/0.94  
% 1.61/0.94  clauses:                                14
% 1.61/0.94  conjectures:                            1
% 1.61/0.94  epr:                                    4
% 1.61/0.94  horn:                                   12
% 1.61/0.94  ground:                                 5
% 1.61/0.94  unary:                                  7
% 1.61/0.94  binary:                                 5
% 1.61/0.94  lits:                                   23
% 1.61/0.94  lits_eq:                                14
% 1.61/0.94  fd_pure:                                0
% 1.61/0.94  fd_pseudo:                              0
% 1.61/0.94  fd_cond:                                1
% 1.61/0.94  fd_pseudo_cond:                         1
% 1.61/0.94  ac_symbols:                             0
% 1.61/0.94  
% 1.61/0.94  ------ Propositional Solver
% 1.61/0.94  
% 1.61/0.94  prop_solver_calls:                      26
% 1.61/0.94  prop_fast_solver_calls:                 326
% 1.61/0.94  smt_solver_calls:                       0
% 1.61/0.94  smt_fast_solver_calls:                  0
% 1.61/0.94  prop_num_of_clauses:                    379
% 1.61/0.94  prop_preprocess_simplified:             1901
% 1.61/0.94  prop_fo_subsumed:                       3
% 1.61/0.94  prop_solver_time:                       0.
% 1.61/0.94  smt_solver_time:                        0.
% 1.61/0.94  smt_fast_solver_time:                   0.
% 1.61/0.94  prop_fast_solver_time:                  0.
% 1.61/0.94  prop_unsat_core_time:                   0.
% 1.61/0.94  
% 1.61/0.94  ------ QBF
% 1.61/0.94  
% 1.61/0.94  qbf_q_res:                              0
% 1.61/0.94  qbf_num_tautologies:                    0
% 1.61/0.94  qbf_prep_cycles:                        0
% 1.61/0.94  
% 1.61/0.94  ------ BMC1
% 1.61/0.94  
% 1.61/0.94  bmc1_current_bound:                     -1
% 1.61/0.94  bmc1_last_solved_bound:                 -1
% 1.61/0.94  bmc1_unsat_core_size:                   -1
% 1.61/0.94  bmc1_unsat_core_parents_size:           -1
% 1.61/0.94  bmc1_merge_next_fun:                    0
% 1.61/0.94  bmc1_unsat_core_clauses_time:           0.
% 1.61/0.94  
% 1.61/0.94  ------ Instantiation
% 1.61/0.94  
% 1.61/0.94  inst_num_of_clauses:                    154
% 1.61/0.94  inst_num_in_passive:                    22
% 1.61/0.94  inst_num_in_active:                     80
% 1.61/0.94  inst_num_in_unprocessed:                52
% 1.61/0.94  inst_num_of_loops:                      90
% 1.61/0.94  inst_num_of_learning_restarts:          0
% 1.61/0.94  inst_num_moves_active_passive:          8
% 1.61/0.94  inst_lit_activity:                      0
% 1.61/0.94  inst_lit_activity_moves:                0
% 1.61/0.94  inst_num_tautologies:                   0
% 1.61/0.94  inst_num_prop_implied:                  0
% 1.61/0.94  inst_num_existing_simplified:           0
% 1.61/0.94  inst_num_eq_res_simplified:             0
% 1.61/0.94  inst_num_child_elim:                    0
% 1.61/0.94  inst_num_of_dismatching_blockings:      4
% 1.61/0.94  inst_num_of_non_proper_insts:           111
% 1.61/0.94  inst_num_of_duplicates:                 0
% 1.61/0.94  inst_inst_num_from_inst_to_res:         0
% 1.61/0.94  inst_dismatching_checking_time:         0.
% 1.61/0.94  
% 1.61/0.94  ------ Resolution
% 1.61/0.94  
% 1.61/0.94  res_num_of_clauses:                     0
% 1.61/0.94  res_num_in_passive:                     0
% 1.61/0.94  res_num_in_active:                      0
% 1.61/0.94  res_num_of_loops:                       79
% 1.61/0.94  res_forward_subset_subsumed:            15
% 1.61/0.94  res_backward_subset_subsumed:           0
% 1.61/0.94  res_forward_subsumed:                   0
% 1.61/0.94  res_backward_subsumed:                  0
% 1.61/0.94  res_forward_subsumption_resolution:     0
% 1.61/0.94  res_backward_subsumption_resolution:    0
% 1.61/0.94  res_clause_to_clause_subsumption:       36
% 1.61/0.94  res_orphan_elimination:                 0
% 1.61/0.94  res_tautology_del:                      5
% 1.61/0.94  res_num_eq_res_simplified:              0
% 1.61/0.94  res_num_sel_changes:                    0
% 1.61/0.94  res_moves_from_active_to_pass:          0
% 1.61/0.94  
% 1.61/0.94  ------ Superposition
% 1.61/0.94  
% 1.61/0.94  sup_time_total:                         0.
% 1.61/0.94  sup_time_generating:                    0.
% 1.61/0.94  sup_time_sim_full:                      0.
% 1.61/0.94  sup_time_sim_immed:                     0.
% 1.61/0.94  
% 1.61/0.94  sup_num_of_clauses:                     14
% 1.61/0.94  sup_num_in_active:                      11
% 1.61/0.94  sup_num_in_passive:                     3
% 1.61/0.94  sup_num_of_loops:                       17
% 1.61/0.94  sup_fw_superposition:                   5
% 1.61/0.94  sup_bw_superposition:                   2
% 1.61/0.94  sup_immediate_simplified:               0
% 1.61/0.94  sup_given_eliminated:                   0
% 1.61/0.94  comparisons_done:                       0
% 1.61/0.94  comparisons_avoided:                    0
% 1.61/0.94  
% 1.61/0.94  ------ Simplifications
% 1.61/0.94  
% 1.61/0.94  
% 1.61/0.94  sim_fw_subset_subsumed:                 0
% 1.61/0.94  sim_bw_subset_subsumed:                 0
% 1.61/0.94  sim_fw_subsumed:                        0
% 1.61/0.94  sim_bw_subsumed:                        0
% 1.61/0.94  sim_fw_subsumption_res:                 1
% 1.61/0.94  sim_bw_subsumption_res:                 0
% 1.61/0.94  sim_tautology_del:                      0
% 1.61/0.94  sim_eq_tautology_del:                   1
% 1.61/0.94  sim_eq_res_simp:                        1
% 1.61/0.94  sim_fw_demodulated:                     3
% 1.61/0.94  sim_bw_demodulated:                     7
% 1.61/0.94  sim_light_normalised:                   2
% 1.61/0.94  sim_joinable_taut:                      0
% 1.61/0.94  sim_joinable_simp:                      0
% 1.61/0.94  sim_ac_normalised:                      0
% 1.61/0.94  sim_smt_subsumption:                    0
% 1.61/0.94  
%------------------------------------------------------------------------------
