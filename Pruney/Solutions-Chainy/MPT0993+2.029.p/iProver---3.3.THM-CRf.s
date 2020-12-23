%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:07 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 241 expanded)
%              Number of clauses        :   49 (  72 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  284 ( 998 expanded)
%              Number of equality atoms :   83 ( 114 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
      & r1_tarski(sK1,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
    & r1_tarski(sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f29])).

fof(f44,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] : k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X3,X2] :
      ( ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
     => k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f27])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_954,plain,
    ( r1_tarski(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_953,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_955,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1258,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_955])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_957,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_959,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1843,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X3)) != iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_959])).

cnf(c_7133,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(X0,sK2)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_1843])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_956,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_7,c_6,c_5])).

cnf(c_952,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_1659,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_952])).

cnf(c_7944,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7133,c_1659])).

cnf(c_8599,plain,
    ( k7_relat_1(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_954,c_7944])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X2,X3)) != k1_funct_1(X2,sK0(X2,X3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_224,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_partfun1(sK1,sK2,sK4,sK3) != X3
    | k1_funct_1(X3,sK0(X3,X0)) != k1_funct_1(X0,sK0(X3,X0))
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_225,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_227,plain,
    ( ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_225,c_14,c_13,c_12])).

cnf(c_228,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_288,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_228])).

cnf(c_311,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_288])).

cnf(c_464,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_311])).

cnf(c_950,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_616,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_464])).

cnf(c_657,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1235,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_1250,plain,
    ( k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_950,c_616,c_1235])).

cnf(c_1251,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_1250])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_277,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_951,plain,
    ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_1105,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_953,c_951])).

cnf(c_1252,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
    | k7_relat_1(sK4,sK3) != sK4 ),
    inference(demodulation,[status(thm)],[c_1251,c_1105])).

cnf(c_8634,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_8599,c_1252])).

cnf(c_9480,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8634])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.32/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/0.98  
% 3.32/0.98  ------  iProver source info
% 3.32/0.98  
% 3.32/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.32/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/0.98  git: non_committed_changes: false
% 3.32/0.98  git: last_make_outside_of_git: false
% 3.32/0.98  
% 3.32/0.98  ------ 
% 3.32/0.98  ------ Parsing...
% 3.32/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/0.98  
% 3.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/0.98  ------ Proving...
% 3.32/0.98  ------ Problem Properties 
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  clauses                                 10
% 3.32/0.98  conjectures                             2
% 3.32/0.98  EPR                                     2
% 3.32/0.98  Horn                                    10
% 3.32/0.98  unary                                   2
% 3.32/0.98  binary                                  6
% 3.32/0.98  lits                                    20
% 3.32/0.98  lits eq                                 4
% 3.32/0.98  fd_pure                                 0
% 3.32/0.98  fd_pseudo                               0
% 3.32/0.98  fd_cond                                 0
% 3.32/0.98  fd_pseudo_cond                          0
% 3.32/0.98  AC symbols                              0
% 3.32/0.98  
% 3.32/0.98  ------ Input Options Time Limit: Unbounded
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  ------ 
% 3.32/0.98  Current options:
% 3.32/0.98  ------ 
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  ------ Proving...
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  % SZS status Theorem for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98   Resolution empty clause
% 3.32/0.98  
% 3.32/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  fof(f9,conjecture,(
% 3.32/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f10,negated_conjecture,(
% 3.32/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 3.32/0.98    inference(negated_conjecture,[],[f9])).
% 3.32/0.98  
% 3.32/0.98  fof(f24,plain,(
% 3.32/0.98    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.32/0.98    inference(ennf_transformation,[],[f10])).
% 3.32/0.98  
% 3.32/0.98  fof(f25,plain,(
% 3.32/0.98    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.32/0.98    inference(flattening,[],[f24])).
% 3.32/0.98  
% 3.32/0.98  fof(f29,plain,(
% 3.32/0.98    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.32/0.98    introduced(choice_axiom,[])).
% 3.32/0.98  
% 3.32/0.98  fof(f30,plain,(
% 3.32/0.98    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.32/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f29])).
% 3.32/0.98  
% 3.32/0.98  fof(f44,plain,(
% 3.32/0.98    r1_tarski(sK1,sK3)),
% 3.32/0.98    inference(cnf_transformation,[],[f30])).
% 3.32/0.98  
% 3.32/0.98  fof(f43,plain,(
% 3.32/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.32/0.98    inference(cnf_transformation,[],[f30])).
% 3.32/0.98  
% 3.32/0.98  fof(f3,axiom,(
% 3.32/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f26,plain,(
% 3.32/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.32/0.98    inference(nnf_transformation,[],[f3])).
% 3.32/0.98  
% 3.32/0.98  fof(f34,plain,(
% 3.32/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.32/0.98    inference(cnf_transformation,[],[f26])).
% 3.32/0.98  
% 3.32/0.98  fof(f2,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f15,plain,(
% 3.32/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.32/0.98    inference(ennf_transformation,[],[f2])).
% 3.32/0.98  
% 3.32/0.98  fof(f32,plain,(
% 3.32/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f15])).
% 3.32/0.98  
% 3.32/0.98  fof(f1,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f13,plain,(
% 3.32/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.32/0.98    inference(ennf_transformation,[],[f1])).
% 3.32/0.98  
% 3.32/0.98  fof(f14,plain,(
% 3.32/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.32/0.98    inference(flattening,[],[f13])).
% 3.32/0.98  
% 3.32/0.98  fof(f31,plain,(
% 3.32/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f14])).
% 3.32/0.98  
% 3.32/0.98  fof(f35,plain,(
% 3.32/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f26])).
% 3.32/0.98  
% 3.32/0.98  fof(f6,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f12,plain,(
% 3.32/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.32/0.98    inference(pure_predicate_removal,[],[f6])).
% 3.32/0.98  
% 3.32/0.98  fof(f19,plain,(
% 3.32/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.98    inference(ennf_transformation,[],[f12])).
% 3.32/0.98  
% 3.32/0.98  fof(f38,plain,(
% 3.32/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.98    inference(cnf_transformation,[],[f19])).
% 3.32/0.98  
% 3.32/0.98  fof(f4,axiom,(
% 3.32/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f16,plain,(
% 3.32/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.32/0.98    inference(ennf_transformation,[],[f4])).
% 3.32/0.98  
% 3.32/0.98  fof(f17,plain,(
% 3.32/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.32/0.98    inference(flattening,[],[f16])).
% 3.32/0.98  
% 3.32/0.98  fof(f36,plain,(
% 3.32/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f17])).
% 3.32/0.98  
% 3.32/0.98  fof(f5,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f18,plain,(
% 3.32/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.32/0.98    inference(ennf_transformation,[],[f5])).
% 3.32/0.98  
% 3.32/0.98  fof(f37,plain,(
% 3.32/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.32/0.98    inference(cnf_transformation,[],[f18])).
% 3.32/0.98  
% 3.32/0.98  fof(f42,plain,(
% 3.32/0.98    v1_funct_2(sK4,sK1,sK2)),
% 3.32/0.98    inference(cnf_transformation,[],[f30])).
% 3.32/0.98  
% 3.32/0.98  fof(f41,plain,(
% 3.32/0.98    v1_funct_1(sK4)),
% 3.32/0.98    inference(cnf_transformation,[],[f30])).
% 3.32/0.98  
% 3.32/0.98  fof(f8,axiom,(
% 3.32/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f11,plain,(
% 3.32/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : k1_funct_1(X2,X4) = k1_funct_1(X3,X4) => r2_relset_1(X0,X1,X2,X3))))),
% 3.32/0.98    inference(pure_predicate_removal,[],[f8])).
% 3.32/0.98  
% 3.32/0.98  fof(f22,plain,(
% 3.32/0.98    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.32/0.98    inference(ennf_transformation,[],[f11])).
% 3.32/0.98  
% 3.32/0.98  fof(f23,plain,(
% 3.32/0.98    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.32/0.98    inference(flattening,[],[f22])).
% 3.32/0.98  
% 3.32/0.98  fof(f27,plain,(
% 3.32/0.98    ! [X3,X2] : (? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4) => k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)))),
% 3.32/0.98    introduced(choice_axiom,[])).
% 3.32/0.98  
% 3.32/0.98  fof(f28,plain,(
% 3.32/0.98    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.32/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f27])).
% 3.32/0.98  
% 3.32/0.98  fof(f40,plain,(
% 3.32/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f28])).
% 3.32/0.98  
% 3.32/0.98  fof(f45,plain,(
% 3.32/0.98    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)),
% 3.32/0.98    inference(cnf_transformation,[],[f30])).
% 3.32/0.98  
% 3.32/0.98  fof(f7,axiom,(
% 3.32/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/0.98  
% 3.32/0.98  fof(f20,plain,(
% 3.32/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.32/0.98    inference(ennf_transformation,[],[f7])).
% 3.32/0.98  
% 3.32/0.98  fof(f21,plain,(
% 3.32/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.32/0.98    inference(flattening,[],[f20])).
% 3.32/0.98  
% 3.32/0.98  fof(f39,plain,(
% 3.32/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.32/0.98    inference(cnf_transformation,[],[f21])).
% 3.32/0.98  
% 3.32/0.98  cnf(c_11,negated_conjecture,
% 3.32/0.98      ( r1_tarski(sK1,sK3) ),
% 3.32/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_954,plain,
% 3.32/0.98      ( r1_tarski(sK1,sK3) = iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_12,negated_conjecture,
% 3.32/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.32/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_953,plain,
% 3.32/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_4,plain,
% 3.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_955,plain,
% 3.32/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.32/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1258,plain,
% 3.32/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_953,c_955]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_2,plain,
% 3.32/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 3.32/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_957,plain,
% 3.32/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.32/0.98      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_0,plain,
% 3.32/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_959,plain,
% 3.32/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.32/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.32/0.98      | r1_tarski(X2,X1) = iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1843,plain,
% 3.32/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.32/0.98      | r1_tarski(X2,k2_zfmisc_1(X0,X3)) != iProver_top
% 3.32/0.98      | r1_tarski(X2,k2_zfmisc_1(X1,X3)) = iProver_top ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_957,c_959]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_7133,plain,
% 3.32/0.98      ( r1_tarski(sK4,k2_zfmisc_1(X0,sK2)) = iProver_top
% 3.32/0.98      | r1_tarski(sK1,X0) != iProver_top ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_1258,c_1843]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_3,plain,
% 3.32/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.32/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_956,plain,
% 3.32/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.32/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_7,plain,
% 3.32/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.32/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_5,plain,
% 3.32/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.32/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_204,plain,
% 3.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.98      | ~ v1_relat_1(X0)
% 3.32/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.32/0.98      inference(resolution,[status(thm)],[c_7,c_5]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_6,plain,
% 3.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.32/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_208,plain,
% 3.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.32/0.98      inference(global_propositional_subsumption,
% 3.32/0.98                [status(thm)],
% 3.32/0.98                [c_204,c_7,c_6,c_5]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_952,plain,
% 3.32/0.98      ( k7_relat_1(X0,X1) = X0
% 3.32/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1659,plain,
% 3.32/0.98      ( k7_relat_1(X0,X1) = X0
% 3.32/0.98      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_956,c_952]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_7944,plain,
% 3.32/0.98      ( k7_relat_1(sK4,X0) = sK4 | r1_tarski(sK1,X0) != iProver_top ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_7133,c_1659]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_8599,plain,
% 3.32/0.98      ( k7_relat_1(sK4,sK3) = sK4 ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_954,c_7944]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_13,negated_conjecture,
% 3.32/0.98      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.32/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_14,negated_conjecture,
% 3.32/0.98      ( v1_funct_1(sK4) ),
% 3.32/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_9,plain,
% 3.32/0.98      ( r2_relset_1(X0,X1,X2,X3)
% 3.32/0.98      | ~ v1_funct_2(X3,X0,X1)
% 3.32/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.32/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.32/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.32/0.98      | ~ v1_funct_1(X2)
% 3.32/0.98      | ~ v1_funct_1(X3)
% 3.32/0.98      | k1_funct_1(X3,sK0(X2,X3)) != k1_funct_1(X2,sK0(X2,X3)) ),
% 3.32/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_10,negated_conjecture,
% 3.32/0.98      ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
% 3.32/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_224,plain,
% 3.32/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.32/0.98      | ~ v1_funct_2(X3,X1,X2)
% 3.32/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.98      | ~ v1_funct_1(X0)
% 3.32/0.98      | ~ v1_funct_1(X3)
% 3.32/0.98      | k2_partfun1(sK1,sK2,sK4,sK3) != X3
% 3.32/0.98      | k1_funct_1(X3,sK0(X3,X0)) != k1_funct_1(X0,sK0(X3,X0))
% 3.32/0.98      | sK4 != X0
% 3.32/0.98      | sK2 != X2
% 3.32/0.98      | sK1 != X1 ),
% 3.32/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_225,plain,
% 3.32/0.98      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 3.32/0.98      | ~ v1_funct_2(sK4,sK1,sK2)
% 3.32/0.98      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.98      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.98      | ~ v1_funct_1(sK4)
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 3.32/0.98      inference(unflattening,[status(thm)],[c_224]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_227,plain,
% 3.32/0.98      ( ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.98      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 3.32/0.98      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 3.32/0.98      inference(global_propositional_subsumption,
% 3.32/0.98                [status(thm)],
% 3.32/0.98                [c_225,c_14,c_13,c_12]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_228,plain,
% 3.32/0.98      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 3.32/0.98      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.98      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 3.32/0.98      inference(renaming,[status(thm)],[c_227]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_288,plain,
% 3.32/0.98      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 3.32/0.98      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.98      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 3.32/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_228]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_311,plain,
% 3.32/0.98      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.98      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 3.32/0.98      | sK2 != sK2
% 3.32/0.98      | sK1 != sK1 ),
% 3.32/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_288]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_464,plain,
% 3.32/0.98      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.32/0.98      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 3.32/0.98      inference(equality_resolution_simp,[status(thm)],[c_311]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_950,plain,
% 3.32/0.98      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 3.32/0.98      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_616,plain,
% 3.32/0.98      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 3.32/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.32/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_464]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_657,plain,( X0 = X0 ),theory(equality) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1235,plain,
% 3.32/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.32/0.98      inference(instantiation,[status(thm)],[c_657]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1250,plain,
% 3.32/0.98      ( k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 3.32/0.98      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4 ),
% 3.32/0.98      inference(global_propositional_subsumption,
% 3.32/0.98                [status(thm)],
% 3.32/0.98                [c_950,c_616,c_1235]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1251,plain,
% 3.32/0.98      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 3.32/0.98      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 3.32/0.98      inference(renaming,[status(thm)],[c_1250]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_8,plain,
% 3.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.98      | ~ v1_funct_1(X0)
% 3.32/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.32/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_276,plain,
% 3.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.32/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.32/0.98      | sK4 != X0 ),
% 3.32/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_277,plain,
% 3.32/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.32/0.98      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 3.32/0.98      inference(unflattening,[status(thm)],[c_276]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_951,plain,
% 3.32/0.98      ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 3.32/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.32/0.98      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1105,plain,
% 3.32/0.98      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.32/0.98      inference(superposition,[status(thm)],[c_953,c_951]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_1252,plain,
% 3.32/0.98      ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
% 3.32/0.98      | k7_relat_1(sK4,sK3) != sK4 ),
% 3.32/0.98      inference(demodulation,[status(thm)],[c_1251,c_1105]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_8634,plain,
% 3.32/0.98      ( k1_funct_1(sK4,sK0(sK4,sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
% 3.32/0.98      | sK4 != sK4 ),
% 3.32/0.98      inference(demodulation,[status(thm)],[c_8599,c_1252]) ).
% 3.32/0.98  
% 3.32/0.98  cnf(c_9480,plain,
% 3.32/0.98      ( $false ),
% 3.32/0.98      inference(equality_resolution_simp,[status(thm)],[c_8634]) ).
% 3.32/0.98  
% 3.32/0.98  
% 3.32/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/0.98  
% 3.32/0.98  ------                               Statistics
% 3.32/0.98  
% 3.32/0.98  ------ Selected
% 3.32/0.98  
% 3.32/0.98  total_time:                             0.285
% 3.32/0.98  
%------------------------------------------------------------------------------
