%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:05 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 461 expanded)
%              Number of clauses        :   87 ( 197 expanded)
%              Number of leaves         :   13 (  84 expanded)
%              Depth                    :   22
%              Number of atoms          :  382 (1620 expanded)
%              Number of equality atoms :  147 ( 291 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,
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

fof(f29,plain,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
    & r1_tarski(sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f28])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
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

fof(f10,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X3,X2] :
      ( ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
     => k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f26])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_268,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_269,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_336,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_269])).

cnf(c_337,plain,
    ( ~ v4_relat_1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_532,plain,
    ( ~ v4_relat_1(sK4,X0_47)
    | r1_tarski(k1_relat_1(sK4),X0_47)
    | k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_540,plain,
    ( ~ v4_relat_1(sK4,X0_47)
    | r1_tarski(k1_relat_1(sK4),X0_47)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_532])).

cnf(c_779,plain,
    ( v4_relat_1(sK4,X0_47) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0_47) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_558,plain,
    ( k2_zfmisc_1(X0_47,X0_48) = k2_zfmisc_1(X1_47,X0_48)
    | X0_47 != X1_47 ),
    theory(equality)).

cnf(c_567,plain,
    ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_546,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_574,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_321,plain,
    ( ~ v4_relat_1(X0,X1)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_269])).

cnf(c_322,plain,
    ( ~ v4_relat_1(sK4,X0)
    | k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_533,plain,
    ( ~ v4_relat_1(sK4,X0_47)
    | k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k7_relat_1(sK4,X0_47) = sK4 ),
    inference(subtyping,[status(esa)],[c_322])).

cnf(c_537,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_533])).

cnf(c_588,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_590,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_541,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_532])).

cnf(c_591,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_592,plain,
    ( v4_relat_1(sK4,X0_47) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0_47) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_559,plain,
    ( X0_52 != X1_52
    | k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) ),
    theory(equality)).

cnf(c_867,plain,
    ( k2_zfmisc_1(X0_47,X0_48) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_868,plain,
    ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_1044,plain,
    ( r1_tarski(k1_relat_1(sK4),X0_47) = iProver_top
    | v4_relat_1(sK4,X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_779,c_567,c_574,c_590,c_591,c_592,c_868])).

cnf(c_1045,plain,
    ( v4_relat_1(sK4,X0_47) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0_47) = iProver_top ),
    inference(renaming,[status(thm)],[c_1044])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_535,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_773,plain,
    ( r1_tarski(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_536,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | ~ r1_tarski(X2_47,X0_47)
    | r1_tarski(X2_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_772,plain,
    ( r1_tarski(X0_47,X1_47) != iProver_top
    | r1_tarski(X2_47,X0_47) != iProver_top
    | r1_tarski(X2_47,X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_948,plain,
    ( r1_tarski(X0_47,sK3) = iProver_top
    | r1_tarski(X0_47,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_772])).

cnf(c_1053,plain,
    ( v4_relat_1(sK4,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_948])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_256,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_257,plain,
    ( v4_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_534,plain,
    ( v4_relat_1(sK4,X0_47)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_257])).

cnf(c_774,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | v4_relat_1(sK4,X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_865,plain,
    ( v4_relat_1(sK4,sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_774])).

cnf(c_1131,plain,
    ( r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_865])).

cnf(c_1,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_351,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_269])).

cnf(c_352,plain,
    ( v4_relat_1(sK4,X0)
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_531,plain,
    ( v4_relat_1(sK4,X0_47)
    | ~ r1_tarski(k1_relat_1(sK4),X0_47)
    | k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_352])).

cnf(c_542,plain,
    ( v4_relat_1(sK4,X0_47)
    | ~ r1_tarski(k1_relat_1(sK4),X0_47)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_531])).

cnf(c_782,plain,
    ( v4_relat_1(sK4,X0_47) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0_47) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_543,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_531])).

cnf(c_596,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_597,plain,
    ( v4_relat_1(sK4,X0_47) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0_47) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_1139,plain,
    ( r1_tarski(k1_relat_1(sK4),X0_47) != iProver_top
    | v4_relat_1(sK4,X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_567,c_574,c_590,c_596,c_597,c_868])).

cnf(c_1140,plain,
    ( v4_relat_1(sK4,X0_47) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1139])).

cnf(c_1146,plain,
    ( v4_relat_1(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_1140])).

cnf(c_538,plain,
    ( ~ v4_relat_1(sK4,X0_47)
    | k7_relat_1(sK4,X0_47) = sK4
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_533])).

cnf(c_776,plain,
    ( k7_relat_1(sK4,X0_47) = sK4
    | v4_relat_1(sK4,X0_47) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_539,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_533])).

cnf(c_584,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_585,plain,
    ( k7_relat_1(sK4,X0_47) = sK4
    | v4_relat_1(sK4,X0_47) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_914,plain,
    ( v4_relat_1(sK4,X0_47) != iProver_top
    | k7_relat_1(sK4,X0_47) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_567,c_574,c_584,c_585,c_590,c_868])).

cnf(c_915,plain,
    ( k7_relat_1(sK4,X0_47) = sK4
    | v4_relat_1(sK4,X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_914])).

cnf(c_1284,plain,
    ( k7_relat_1(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_1146,c_915])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_198,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_296,plain,
    ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_198])).

cnf(c_438,plain,
    ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_296])).

cnf(c_530,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k2_partfun1(X0_47,X0_48,sK4,X1_47) = k7_relat_1(sK4,X1_47) ),
    inference(subtyping,[status(esa)],[c_438])).

cnf(c_879,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0_47) = k7_relat_1(sK4,X0_47) ),
    inference(equality_resolution,[status(thm)],[c_530])).

cnf(c_11,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X2,X3)) != k1_funct_1(X2,sK0(X2,X3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_145,plain,
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
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_146,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_148,plain,
    ( ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_146,c_12,c_11,c_10])).

cnf(c_149,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_148])).

cnf(c_209,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_149])).

cnf(c_232,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_209])).

cnf(c_280,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_232])).

cnf(c_440,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_280])).

cnf(c_529,plain,
    ( k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4 ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_896,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
    | k7_relat_1(sK4,sK3) != sK4 ),
    inference(demodulation,[status(thm)],[c_879,c_529])).

cnf(c_1286,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_1284,c_896])).

cnf(c_1338,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1286])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:53:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 0.99/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.99/1.00  
% 0.99/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.99/1.00  
% 0.99/1.00  ------  iProver source info
% 0.99/1.00  
% 0.99/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.99/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.99/1.00  git: non_committed_changes: false
% 0.99/1.00  git: last_make_outside_of_git: false
% 0.99/1.00  
% 0.99/1.00  ------ 
% 0.99/1.00  
% 0.99/1.00  ------ Input Options
% 0.99/1.00  
% 0.99/1.00  --out_options                           all
% 0.99/1.00  --tptp_safe_out                         true
% 0.99/1.00  --problem_path                          ""
% 0.99/1.00  --include_path                          ""
% 0.99/1.00  --clausifier                            res/vclausify_rel
% 0.99/1.00  --clausifier_options                    --mode clausify
% 0.99/1.00  --stdin                                 false
% 0.99/1.00  --stats_out                             all
% 0.99/1.00  
% 0.99/1.00  ------ General Options
% 0.99/1.00  
% 0.99/1.00  --fof                                   false
% 0.99/1.00  --time_out_real                         305.
% 0.99/1.00  --time_out_virtual                      -1.
% 0.99/1.00  --symbol_type_check                     false
% 0.99/1.00  --clausify_out                          false
% 0.99/1.00  --sig_cnt_out                           false
% 0.99/1.00  --trig_cnt_out                          false
% 0.99/1.00  --trig_cnt_out_tolerance                1.
% 0.99/1.00  --trig_cnt_out_sk_spl                   false
% 0.99/1.00  --abstr_cl_out                          false
% 0.99/1.00  
% 0.99/1.00  ------ Global Options
% 0.99/1.00  
% 0.99/1.00  --schedule                              default
% 0.99/1.00  --add_important_lit                     false
% 0.99/1.00  --prop_solver_per_cl                    1000
% 0.99/1.00  --min_unsat_core                        false
% 0.99/1.00  --soft_assumptions                      false
% 0.99/1.00  --soft_lemma_size                       3
% 0.99/1.00  --prop_impl_unit_size                   0
% 0.99/1.00  --prop_impl_unit                        []
% 0.99/1.00  --share_sel_clauses                     true
% 0.99/1.00  --reset_solvers                         false
% 0.99/1.00  --bc_imp_inh                            [conj_cone]
% 0.99/1.00  --conj_cone_tolerance                   3.
% 0.99/1.00  --extra_neg_conj                        none
% 0.99/1.00  --large_theory_mode                     true
% 0.99/1.00  --prolific_symb_bound                   200
% 0.99/1.00  --lt_threshold                          2000
% 0.99/1.00  --clause_weak_htbl                      true
% 0.99/1.00  --gc_record_bc_elim                     false
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing Options
% 0.99/1.00  
% 0.99/1.00  --preprocessing_flag                    true
% 0.99/1.00  --time_out_prep_mult                    0.1
% 0.99/1.00  --splitting_mode                        input
% 0.99/1.00  --splitting_grd                         true
% 0.99/1.00  --splitting_cvd                         false
% 0.99/1.00  --splitting_cvd_svl                     false
% 0.99/1.00  --splitting_nvd                         32
% 0.99/1.00  --sub_typing                            true
% 0.99/1.00  --prep_gs_sim                           true
% 0.99/1.00  --prep_unflatten                        true
% 0.99/1.00  --prep_res_sim                          true
% 0.99/1.00  --prep_upred                            true
% 0.99/1.00  --prep_sem_filter                       exhaustive
% 0.99/1.00  --prep_sem_filter_out                   false
% 0.99/1.00  --pred_elim                             true
% 0.99/1.00  --res_sim_input                         true
% 0.99/1.00  --eq_ax_congr_red                       true
% 0.99/1.00  --pure_diseq_elim                       true
% 0.99/1.00  --brand_transform                       false
% 0.99/1.00  --non_eq_to_eq                          false
% 0.99/1.00  --prep_def_merge                        true
% 0.99/1.00  --prep_def_merge_prop_impl              false
% 0.99/1.00  --prep_def_merge_mbd                    true
% 0.99/1.00  --prep_def_merge_tr_red                 false
% 0.99/1.00  --prep_def_merge_tr_cl                  false
% 0.99/1.00  --smt_preprocessing                     true
% 0.99/1.00  --smt_ac_axioms                         fast
% 0.99/1.00  --preprocessed_out                      false
% 0.99/1.00  --preprocessed_stats                    false
% 0.99/1.00  
% 0.99/1.00  ------ Abstraction refinement Options
% 0.99/1.00  
% 0.99/1.00  --abstr_ref                             []
% 0.99/1.00  --abstr_ref_prep                        false
% 0.99/1.00  --abstr_ref_until_sat                   false
% 0.99/1.00  --abstr_ref_sig_restrict                funpre
% 0.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.00  --abstr_ref_under                       []
% 0.99/1.00  
% 0.99/1.00  ------ SAT Options
% 0.99/1.00  
% 0.99/1.00  --sat_mode                              false
% 0.99/1.00  --sat_fm_restart_options                ""
% 0.99/1.00  --sat_gr_def                            false
% 0.99/1.00  --sat_epr_types                         true
% 0.99/1.00  --sat_non_cyclic_types                  false
% 0.99/1.00  --sat_finite_models                     false
% 0.99/1.00  --sat_fm_lemmas                         false
% 0.99/1.00  --sat_fm_prep                           false
% 0.99/1.00  --sat_fm_uc_incr                        true
% 0.99/1.00  --sat_out_model                         small
% 0.99/1.00  --sat_out_clauses                       false
% 0.99/1.00  
% 0.99/1.00  ------ QBF Options
% 0.99/1.00  
% 0.99/1.00  --qbf_mode                              false
% 0.99/1.00  --qbf_elim_univ                         false
% 0.99/1.00  --qbf_dom_inst                          none
% 0.99/1.00  --qbf_dom_pre_inst                      false
% 0.99/1.00  --qbf_sk_in                             false
% 0.99/1.00  --qbf_pred_elim                         true
% 0.99/1.00  --qbf_split                             512
% 0.99/1.00  
% 0.99/1.00  ------ BMC1 Options
% 0.99/1.00  
% 0.99/1.00  --bmc1_incremental                      false
% 0.99/1.00  --bmc1_axioms                           reachable_all
% 0.99/1.00  --bmc1_min_bound                        0
% 0.99/1.00  --bmc1_max_bound                        -1
% 0.99/1.00  --bmc1_max_bound_default                -1
% 0.99/1.00  --bmc1_symbol_reachability              true
% 0.99/1.00  --bmc1_property_lemmas                  false
% 0.99/1.00  --bmc1_k_induction                      false
% 0.99/1.00  --bmc1_non_equiv_states                 false
% 0.99/1.00  --bmc1_deadlock                         false
% 0.99/1.00  --bmc1_ucm                              false
% 0.99/1.00  --bmc1_add_unsat_core                   none
% 0.99/1.00  --bmc1_unsat_core_children              false
% 0.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.00  --bmc1_out_stat                         full
% 0.99/1.00  --bmc1_ground_init                      false
% 0.99/1.00  --bmc1_pre_inst_next_state              false
% 0.99/1.00  --bmc1_pre_inst_state                   false
% 0.99/1.00  --bmc1_pre_inst_reach_state             false
% 0.99/1.00  --bmc1_out_unsat_core                   false
% 0.99/1.00  --bmc1_aig_witness_out                  false
% 0.99/1.00  --bmc1_verbose                          false
% 0.99/1.00  --bmc1_dump_clauses_tptp                false
% 0.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.00  --bmc1_dump_file                        -
% 0.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.00  --bmc1_ucm_extend_mode                  1
% 0.99/1.00  --bmc1_ucm_init_mode                    2
% 0.99/1.00  --bmc1_ucm_cone_mode                    none
% 0.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.00  --bmc1_ucm_relax_model                  4
% 0.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.00  --bmc1_ucm_layered_model                none
% 0.99/1.00  --bmc1_ucm_max_lemma_size               10
% 0.99/1.00  
% 0.99/1.00  ------ AIG Options
% 0.99/1.00  
% 0.99/1.00  --aig_mode                              false
% 0.99/1.00  
% 0.99/1.00  ------ Instantiation Options
% 0.99/1.00  
% 0.99/1.00  --instantiation_flag                    true
% 0.99/1.00  --inst_sos_flag                         false
% 0.99/1.00  --inst_sos_phase                        true
% 0.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.00  --inst_lit_sel_side                     num_symb
% 0.99/1.00  --inst_solver_per_active                1400
% 0.99/1.00  --inst_solver_calls_frac                1.
% 0.99/1.00  --inst_passive_queue_type               priority_queues
% 0.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.00  --inst_passive_queues_freq              [25;2]
% 0.99/1.00  --inst_dismatching                      true
% 0.99/1.00  --inst_eager_unprocessed_to_passive     true
% 0.99/1.00  --inst_prop_sim_given                   true
% 0.99/1.00  --inst_prop_sim_new                     false
% 0.99/1.00  --inst_subs_new                         false
% 0.99/1.00  --inst_eq_res_simp                      false
% 0.99/1.00  --inst_subs_given                       false
% 0.99/1.00  --inst_orphan_elimination               true
% 0.99/1.00  --inst_learning_loop_flag               true
% 0.99/1.00  --inst_learning_start                   3000
% 0.99/1.00  --inst_learning_factor                  2
% 0.99/1.00  --inst_start_prop_sim_after_learn       3
% 0.99/1.00  --inst_sel_renew                        solver
% 0.99/1.00  --inst_lit_activity_flag                true
% 0.99/1.00  --inst_restr_to_given                   false
% 0.99/1.00  --inst_activity_threshold               500
% 0.99/1.00  --inst_out_proof                        true
% 0.99/1.00  
% 0.99/1.00  ------ Resolution Options
% 0.99/1.00  
% 0.99/1.00  --resolution_flag                       true
% 0.99/1.00  --res_lit_sel                           adaptive
% 0.99/1.00  --res_lit_sel_side                      none
% 0.99/1.00  --res_ordering                          kbo
% 0.99/1.00  --res_to_prop_solver                    active
% 0.99/1.00  --res_prop_simpl_new                    false
% 0.99/1.00  --res_prop_simpl_given                  true
% 0.99/1.00  --res_passive_queue_type                priority_queues
% 0.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.00  --res_passive_queues_freq               [15;5]
% 0.99/1.00  --res_forward_subs                      full
% 0.99/1.00  --res_backward_subs                     full
% 0.99/1.00  --res_forward_subs_resolution           true
% 0.99/1.00  --res_backward_subs_resolution          true
% 0.99/1.00  --res_orphan_elimination                true
% 0.99/1.00  --res_time_limit                        2.
% 0.99/1.00  --res_out_proof                         true
% 0.99/1.00  
% 0.99/1.00  ------ Superposition Options
% 0.99/1.00  
% 0.99/1.00  --superposition_flag                    true
% 0.99/1.00  --sup_passive_queue_type                priority_queues
% 0.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.00  --demod_completeness_check              fast
% 0.99/1.00  --demod_use_ground                      true
% 0.99/1.00  --sup_to_prop_solver                    passive
% 0.99/1.00  --sup_prop_simpl_new                    true
% 0.99/1.00  --sup_prop_simpl_given                  true
% 0.99/1.00  --sup_fun_splitting                     false
% 0.99/1.00  --sup_smt_interval                      50000
% 0.99/1.00  
% 0.99/1.00  ------ Superposition Simplification Setup
% 0.99/1.00  
% 0.99/1.00  --sup_indices_passive                   []
% 0.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_full_bw                           [BwDemod]
% 0.99/1.00  --sup_immed_triv                        [TrivRules]
% 0.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_immed_bw_main                     []
% 0.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.00  
% 0.99/1.00  ------ Combination Options
% 0.99/1.00  
% 0.99/1.00  --comb_res_mult                         3
% 0.99/1.00  --comb_sup_mult                         2
% 0.99/1.00  --comb_inst_mult                        10
% 0.99/1.00  
% 0.99/1.00  ------ Debug Options
% 0.99/1.00  
% 0.99/1.00  --dbg_backtrace                         false
% 0.99/1.00  --dbg_dump_prop_clauses                 false
% 0.99/1.00  --dbg_dump_prop_clauses_file            -
% 0.99/1.00  --dbg_out_stat                          false
% 0.99/1.00  ------ Parsing...
% 0.99/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.99/1.00  ------ Proving...
% 0.99/1.00  ------ Problem Properties 
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  clauses                                 14
% 0.99/1.00  conjectures                             1
% 0.99/1.00  EPR                                     5
% 0.99/1.00  Horn                                    11
% 0.99/1.00  unary                                   1
% 0.99/1.00  binary                                  9
% 0.99/1.00  lits                                    31
% 0.99/1.00  lits eq                                 9
% 0.99/1.00  fd_pure                                 0
% 0.99/1.00  fd_pseudo                               0
% 0.99/1.00  fd_cond                                 0
% 0.99/1.00  fd_pseudo_cond                          0
% 0.99/1.00  AC symbols                              0
% 0.99/1.00  
% 0.99/1.00  ------ Schedule dynamic 5 is on 
% 0.99/1.00  
% 0.99/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  ------ 
% 0.99/1.00  Current options:
% 0.99/1.00  ------ 
% 0.99/1.00  
% 0.99/1.00  ------ Input Options
% 0.99/1.00  
% 0.99/1.00  --out_options                           all
% 0.99/1.00  --tptp_safe_out                         true
% 0.99/1.00  --problem_path                          ""
% 0.99/1.00  --include_path                          ""
% 0.99/1.00  --clausifier                            res/vclausify_rel
% 0.99/1.00  --clausifier_options                    --mode clausify
% 0.99/1.00  --stdin                                 false
% 0.99/1.00  --stats_out                             all
% 0.99/1.00  
% 0.99/1.00  ------ General Options
% 0.99/1.00  
% 0.99/1.00  --fof                                   false
% 0.99/1.00  --time_out_real                         305.
% 0.99/1.00  --time_out_virtual                      -1.
% 0.99/1.00  --symbol_type_check                     false
% 0.99/1.00  --clausify_out                          false
% 0.99/1.00  --sig_cnt_out                           false
% 0.99/1.00  --trig_cnt_out                          false
% 0.99/1.00  --trig_cnt_out_tolerance                1.
% 0.99/1.00  --trig_cnt_out_sk_spl                   false
% 0.99/1.00  --abstr_cl_out                          false
% 0.99/1.00  
% 0.99/1.00  ------ Global Options
% 0.99/1.00  
% 0.99/1.00  --schedule                              default
% 0.99/1.00  --add_important_lit                     false
% 0.99/1.00  --prop_solver_per_cl                    1000
% 0.99/1.00  --min_unsat_core                        false
% 0.99/1.00  --soft_assumptions                      false
% 0.99/1.00  --soft_lemma_size                       3
% 0.99/1.00  --prop_impl_unit_size                   0
% 0.99/1.00  --prop_impl_unit                        []
% 0.99/1.00  --share_sel_clauses                     true
% 0.99/1.00  --reset_solvers                         false
% 0.99/1.00  --bc_imp_inh                            [conj_cone]
% 0.99/1.00  --conj_cone_tolerance                   3.
% 0.99/1.00  --extra_neg_conj                        none
% 0.99/1.00  --large_theory_mode                     true
% 0.99/1.00  --prolific_symb_bound                   200
% 0.99/1.00  --lt_threshold                          2000
% 0.99/1.00  --clause_weak_htbl                      true
% 0.99/1.00  --gc_record_bc_elim                     false
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing Options
% 0.99/1.00  
% 0.99/1.00  --preprocessing_flag                    true
% 0.99/1.00  --time_out_prep_mult                    0.1
% 0.99/1.00  --splitting_mode                        input
% 0.99/1.00  --splitting_grd                         true
% 0.99/1.00  --splitting_cvd                         false
% 0.99/1.00  --splitting_cvd_svl                     false
% 0.99/1.00  --splitting_nvd                         32
% 0.99/1.00  --sub_typing                            true
% 0.99/1.00  --prep_gs_sim                           true
% 0.99/1.00  --prep_unflatten                        true
% 0.99/1.00  --prep_res_sim                          true
% 0.99/1.00  --prep_upred                            true
% 0.99/1.00  --prep_sem_filter                       exhaustive
% 0.99/1.00  --prep_sem_filter_out                   false
% 0.99/1.00  --pred_elim                             true
% 0.99/1.00  --res_sim_input                         true
% 0.99/1.00  --eq_ax_congr_red                       true
% 0.99/1.00  --pure_diseq_elim                       true
% 0.99/1.00  --brand_transform                       false
% 0.99/1.00  --non_eq_to_eq                          false
% 0.99/1.00  --prep_def_merge                        true
% 0.99/1.00  --prep_def_merge_prop_impl              false
% 0.99/1.00  --prep_def_merge_mbd                    true
% 0.99/1.00  --prep_def_merge_tr_red                 false
% 0.99/1.00  --prep_def_merge_tr_cl                  false
% 0.99/1.00  --smt_preprocessing                     true
% 0.99/1.00  --smt_ac_axioms                         fast
% 0.99/1.00  --preprocessed_out                      false
% 0.99/1.00  --preprocessed_stats                    false
% 0.99/1.00  
% 0.99/1.00  ------ Abstraction refinement Options
% 0.99/1.00  
% 0.99/1.00  --abstr_ref                             []
% 0.99/1.00  --abstr_ref_prep                        false
% 0.99/1.00  --abstr_ref_until_sat                   false
% 0.99/1.00  --abstr_ref_sig_restrict                funpre
% 0.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.00  --abstr_ref_under                       []
% 0.99/1.00  
% 0.99/1.00  ------ SAT Options
% 0.99/1.00  
% 0.99/1.00  --sat_mode                              false
% 0.99/1.00  --sat_fm_restart_options                ""
% 0.99/1.00  --sat_gr_def                            false
% 0.99/1.00  --sat_epr_types                         true
% 0.99/1.00  --sat_non_cyclic_types                  false
% 0.99/1.00  --sat_finite_models                     false
% 0.99/1.00  --sat_fm_lemmas                         false
% 0.99/1.00  --sat_fm_prep                           false
% 0.99/1.00  --sat_fm_uc_incr                        true
% 0.99/1.00  --sat_out_model                         small
% 0.99/1.00  --sat_out_clauses                       false
% 0.99/1.00  
% 0.99/1.00  ------ QBF Options
% 0.99/1.00  
% 0.99/1.00  --qbf_mode                              false
% 0.99/1.00  --qbf_elim_univ                         false
% 0.99/1.00  --qbf_dom_inst                          none
% 0.99/1.00  --qbf_dom_pre_inst                      false
% 0.99/1.00  --qbf_sk_in                             false
% 0.99/1.00  --qbf_pred_elim                         true
% 0.99/1.00  --qbf_split                             512
% 0.99/1.00  
% 0.99/1.00  ------ BMC1 Options
% 0.99/1.00  
% 0.99/1.00  --bmc1_incremental                      false
% 0.99/1.00  --bmc1_axioms                           reachable_all
% 0.99/1.00  --bmc1_min_bound                        0
% 0.99/1.00  --bmc1_max_bound                        -1
% 0.99/1.00  --bmc1_max_bound_default                -1
% 0.99/1.00  --bmc1_symbol_reachability              true
% 0.99/1.00  --bmc1_property_lemmas                  false
% 0.99/1.00  --bmc1_k_induction                      false
% 0.99/1.00  --bmc1_non_equiv_states                 false
% 0.99/1.00  --bmc1_deadlock                         false
% 0.99/1.00  --bmc1_ucm                              false
% 0.99/1.00  --bmc1_add_unsat_core                   none
% 0.99/1.00  --bmc1_unsat_core_children              false
% 0.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.00  --bmc1_out_stat                         full
% 0.99/1.00  --bmc1_ground_init                      false
% 0.99/1.00  --bmc1_pre_inst_next_state              false
% 0.99/1.00  --bmc1_pre_inst_state                   false
% 0.99/1.00  --bmc1_pre_inst_reach_state             false
% 0.99/1.00  --bmc1_out_unsat_core                   false
% 0.99/1.00  --bmc1_aig_witness_out                  false
% 0.99/1.00  --bmc1_verbose                          false
% 0.99/1.00  --bmc1_dump_clauses_tptp                false
% 0.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.00  --bmc1_dump_file                        -
% 0.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.00  --bmc1_ucm_extend_mode                  1
% 0.99/1.00  --bmc1_ucm_init_mode                    2
% 0.99/1.00  --bmc1_ucm_cone_mode                    none
% 0.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.00  --bmc1_ucm_relax_model                  4
% 0.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.00  --bmc1_ucm_layered_model                none
% 0.99/1.00  --bmc1_ucm_max_lemma_size               10
% 0.99/1.00  
% 0.99/1.00  ------ AIG Options
% 0.99/1.00  
% 0.99/1.00  --aig_mode                              false
% 0.99/1.00  
% 0.99/1.00  ------ Instantiation Options
% 0.99/1.00  
% 0.99/1.00  --instantiation_flag                    true
% 0.99/1.00  --inst_sos_flag                         false
% 0.99/1.00  --inst_sos_phase                        true
% 0.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.00  --inst_lit_sel_side                     none
% 0.99/1.00  --inst_solver_per_active                1400
% 0.99/1.00  --inst_solver_calls_frac                1.
% 0.99/1.00  --inst_passive_queue_type               priority_queues
% 0.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.00  --inst_passive_queues_freq              [25;2]
% 0.99/1.00  --inst_dismatching                      true
% 0.99/1.00  --inst_eager_unprocessed_to_passive     true
% 0.99/1.00  --inst_prop_sim_given                   true
% 0.99/1.00  --inst_prop_sim_new                     false
% 0.99/1.00  --inst_subs_new                         false
% 0.99/1.00  --inst_eq_res_simp                      false
% 0.99/1.00  --inst_subs_given                       false
% 0.99/1.00  --inst_orphan_elimination               true
% 0.99/1.00  --inst_learning_loop_flag               true
% 0.99/1.00  --inst_learning_start                   3000
% 0.99/1.00  --inst_learning_factor                  2
% 0.99/1.00  --inst_start_prop_sim_after_learn       3
% 0.99/1.00  --inst_sel_renew                        solver
% 0.99/1.00  --inst_lit_activity_flag                true
% 0.99/1.00  --inst_restr_to_given                   false
% 0.99/1.00  --inst_activity_threshold               500
% 0.99/1.00  --inst_out_proof                        true
% 0.99/1.00  
% 0.99/1.00  ------ Resolution Options
% 0.99/1.00  
% 0.99/1.00  --resolution_flag                       false
% 0.99/1.00  --res_lit_sel                           adaptive
% 0.99/1.00  --res_lit_sel_side                      none
% 0.99/1.00  --res_ordering                          kbo
% 0.99/1.00  --res_to_prop_solver                    active
% 0.99/1.00  --res_prop_simpl_new                    false
% 0.99/1.00  --res_prop_simpl_given                  true
% 0.99/1.00  --res_passive_queue_type                priority_queues
% 0.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.00  --res_passive_queues_freq               [15;5]
% 0.99/1.00  --res_forward_subs                      full
% 0.99/1.00  --res_backward_subs                     full
% 0.99/1.00  --res_forward_subs_resolution           true
% 0.99/1.00  --res_backward_subs_resolution          true
% 0.99/1.00  --res_orphan_elimination                true
% 0.99/1.00  --res_time_limit                        2.
% 0.99/1.00  --res_out_proof                         true
% 0.99/1.00  
% 0.99/1.00  ------ Superposition Options
% 0.99/1.00  
% 0.99/1.00  --superposition_flag                    true
% 0.99/1.00  --sup_passive_queue_type                priority_queues
% 0.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.00  --demod_completeness_check              fast
% 0.99/1.00  --demod_use_ground                      true
% 0.99/1.00  --sup_to_prop_solver                    passive
% 0.99/1.00  --sup_prop_simpl_new                    true
% 0.99/1.00  --sup_prop_simpl_given                  true
% 0.99/1.00  --sup_fun_splitting                     false
% 0.99/1.00  --sup_smt_interval                      50000
% 0.99/1.00  
% 0.99/1.00  ------ Superposition Simplification Setup
% 0.99/1.00  
% 0.99/1.00  --sup_indices_passive                   []
% 0.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_full_bw                           [BwDemod]
% 0.99/1.00  --sup_immed_triv                        [TrivRules]
% 0.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_immed_bw_main                     []
% 0.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.00  
% 0.99/1.00  ------ Combination Options
% 0.99/1.00  
% 0.99/1.00  --comb_res_mult                         3
% 0.99/1.00  --comb_sup_mult                         2
% 0.99/1.00  --comb_inst_mult                        10
% 0.99/1.00  
% 0.99/1.00  ------ Debug Options
% 0.99/1.00  
% 0.99/1.00  --dbg_backtrace                         false
% 0.99/1.00  --dbg_dump_prop_clauses                 false
% 0.99/1.00  --dbg_dump_prop_clauses_file            -
% 0.99/1.00  --dbg_out_stat                          false
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  ------ Proving...
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  % SZS status Theorem for theBenchmark.p
% 0.99/1.00  
% 0.99/1.00   Resolution empty clause
% 0.99/1.00  
% 0.99/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.99/1.00  
% 0.99/1.00  fof(f2,axiom,(
% 0.99/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f14,plain,(
% 0.99/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.99/1.00    inference(ennf_transformation,[],[f2])).
% 0.99/1.00  
% 0.99/1.00  fof(f25,plain,(
% 0.99/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.99/1.00    inference(nnf_transformation,[],[f14])).
% 0.99/1.00  
% 0.99/1.00  fof(f31,plain,(
% 0.99/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.99/1.00    inference(cnf_transformation,[],[f25])).
% 0.99/1.00  
% 0.99/1.00  fof(f4,axiom,(
% 0.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f17,plain,(
% 0.99/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.99/1.00    inference(ennf_transformation,[],[f4])).
% 0.99/1.00  
% 0.99/1.00  fof(f34,plain,(
% 0.99/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.99/1.00    inference(cnf_transformation,[],[f17])).
% 0.99/1.00  
% 0.99/1.00  fof(f8,conjecture,(
% 0.99/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f9,negated_conjecture,(
% 0.99/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.99/1.00    inference(negated_conjecture,[],[f8])).
% 0.99/1.00  
% 0.99/1.00  fof(f23,plain,(
% 0.99/1.00    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.99/1.00    inference(ennf_transformation,[],[f9])).
% 0.99/1.00  
% 0.99/1.00  fof(f24,plain,(
% 0.99/1.00    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.99/1.00    inference(flattening,[],[f23])).
% 0.99/1.00  
% 0.99/1.00  fof(f28,plain,(
% 0.99/1.00    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.99/1.00    introduced(choice_axiom,[])).
% 0.99/1.00  
% 0.99/1.00  fof(f29,plain,(
% 0.99/1.00    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 0.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f28])).
% 0.99/1.00  
% 0.99/1.00  fof(f40,plain,(
% 0.99/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.99/1.00    inference(cnf_transformation,[],[f29])).
% 0.99/1.00  
% 0.99/1.00  fof(f3,axiom,(
% 0.99/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f15,plain,(
% 0.99/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.99/1.00    inference(ennf_transformation,[],[f3])).
% 0.99/1.00  
% 0.99/1.00  fof(f16,plain,(
% 0.99/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.99/1.00    inference(flattening,[],[f15])).
% 0.99/1.00  
% 0.99/1.00  fof(f33,plain,(
% 0.99/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.99/1.00    inference(cnf_transformation,[],[f16])).
% 0.99/1.00  
% 0.99/1.00  fof(f41,plain,(
% 0.99/1.00    r1_tarski(sK1,sK3)),
% 0.99/1.00    inference(cnf_transformation,[],[f29])).
% 0.99/1.00  
% 0.99/1.00  fof(f1,axiom,(
% 0.99/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f12,plain,(
% 0.99/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.99/1.00    inference(ennf_transformation,[],[f1])).
% 0.99/1.00  
% 0.99/1.00  fof(f13,plain,(
% 0.99/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.99/1.00    inference(flattening,[],[f12])).
% 0.99/1.00  
% 0.99/1.00  fof(f30,plain,(
% 0.99/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.99/1.00    inference(cnf_transformation,[],[f13])).
% 0.99/1.00  
% 0.99/1.00  fof(f5,axiom,(
% 0.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f11,plain,(
% 0.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.99/1.00    inference(pure_predicate_removal,[],[f5])).
% 0.99/1.00  
% 0.99/1.00  fof(f18,plain,(
% 0.99/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.99/1.00    inference(ennf_transformation,[],[f11])).
% 0.99/1.00  
% 0.99/1.00  fof(f35,plain,(
% 0.99/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.99/1.00    inference(cnf_transformation,[],[f18])).
% 0.99/1.00  
% 0.99/1.00  fof(f32,plain,(
% 0.99/1.00    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.99/1.00    inference(cnf_transformation,[],[f25])).
% 0.99/1.00  
% 0.99/1.00  fof(f6,axiom,(
% 0.99/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f19,plain,(
% 0.99/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.99/1.00    inference(ennf_transformation,[],[f6])).
% 0.99/1.00  
% 0.99/1.00  fof(f20,plain,(
% 0.99/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.99/1.00    inference(flattening,[],[f19])).
% 0.99/1.00  
% 0.99/1.00  fof(f36,plain,(
% 0.99/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.99/1.00    inference(cnf_transformation,[],[f20])).
% 0.99/1.00  
% 0.99/1.00  fof(f38,plain,(
% 0.99/1.00    v1_funct_1(sK4)),
% 0.99/1.00    inference(cnf_transformation,[],[f29])).
% 0.99/1.00  
% 0.99/1.00  fof(f39,plain,(
% 0.99/1.00    v1_funct_2(sK4,sK1,sK2)),
% 0.99/1.00    inference(cnf_transformation,[],[f29])).
% 0.99/1.00  
% 0.99/1.00  fof(f7,axiom,(
% 0.99/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.99/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.00  
% 0.99/1.00  fof(f10,plain,(
% 0.99/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : k1_funct_1(X2,X4) = k1_funct_1(X3,X4) => r2_relset_1(X0,X1,X2,X3))))),
% 0.99/1.00    inference(pure_predicate_removal,[],[f7])).
% 0.99/1.00  
% 0.99/1.00  fof(f21,plain,(
% 0.99/1.00    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.99/1.00    inference(ennf_transformation,[],[f10])).
% 0.99/1.00  
% 0.99/1.00  fof(f22,plain,(
% 0.99/1.00    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.99/1.00    inference(flattening,[],[f21])).
% 0.99/1.00  
% 0.99/1.00  fof(f26,plain,(
% 0.99/1.00    ! [X3,X2] : (? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4) => k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)))),
% 0.99/1.00    introduced(choice_axiom,[])).
% 0.99/1.00  
% 0.99/1.00  fof(f27,plain,(
% 0.99/1.00    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f26])).
% 0.99/1.00  
% 0.99/1.00  fof(f37,plain,(
% 0.99/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.99/1.00    inference(cnf_transformation,[],[f27])).
% 0.99/1.00  
% 0.99/1.00  fof(f42,plain,(
% 0.99/1.00    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)),
% 0.99/1.00    inference(cnf_transformation,[],[f29])).
% 0.99/1.00  
% 0.99/1.00  cnf(c_2,plain,
% 0.99/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 0.99/1.00      inference(cnf_transformation,[],[f31]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_4,plain,
% 0.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.99/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_10,negated_conjecture,
% 0.99/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 0.99/1.00      inference(cnf_transformation,[],[f40]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_268,plain,
% 0.99/1.00      ( v1_relat_1(X0)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sK4 != X0 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_269,plain,
% 0.99/1.00      ( v1_relat_1(sK4)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(unflattening,[status(thm)],[c_268]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_336,plain,
% 0.99/1.00      ( ~ v4_relat_1(X0,X1)
% 0.99/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sK4 != X0 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_269]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_337,plain,
% 0.99/1.00      ( ~ v4_relat_1(sK4,X0)
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(unflattening,[status(thm)],[c_336]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_532,plain,
% 0.99/1.00      ( ~ v4_relat_1(sK4,X0_47)
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0_47)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(subtyping,[status(esa)],[c_337]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_540,plain,
% 0.99/1.00      ( ~ v4_relat_1(sK4,X0_47)
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0_47)
% 0.99/1.00      | ~ sP2_iProver_split ),
% 0.99/1.00      inference(splitting,
% 0.99/1.00                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 0.99/1.00                [c_532]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_779,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47) != iProver_top
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0_47) = iProver_top
% 0.99/1.00      | sP2_iProver_split != iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_558,plain,
% 0.99/1.00      ( k2_zfmisc_1(X0_47,X0_48) = k2_zfmisc_1(X1_47,X0_48) | X0_47 != X1_47 ),
% 0.99/1.00      theory(equality) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_567,plain,
% 0.99/1.00      ( k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK2) | sK1 != sK1 ),
% 0.99/1.00      inference(instantiation,[status(thm)],[c_558]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_546,plain,( X0_47 = X0_47 ),theory(equality) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_574,plain,
% 0.99/1.00      ( sK1 = sK1 ),
% 0.99/1.00      inference(instantiation,[status(thm)],[c_546]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_3,plain,
% 0.99/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.99/1.00      inference(cnf_transformation,[],[f33]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_321,plain,
% 0.99/1.00      ( ~ v4_relat_1(X0,X1)
% 0.99/1.00      | k7_relat_1(X0,X1) = X0
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sK4 != X0 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_269]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_322,plain,
% 0.99/1.00      ( ~ v4_relat_1(sK4,X0)
% 0.99/1.00      | k7_relat_1(sK4,X0) = sK4
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(unflattening,[status(thm)],[c_321]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_533,plain,
% 0.99/1.00      ( ~ v4_relat_1(sK4,X0_47)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | k7_relat_1(sK4,X0_47) = sK4 ),
% 0.99/1.00      inference(subtyping,[status(esa)],[c_322]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_537,plain,
% 0.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | ~ sP0_iProver_split ),
% 0.99/1.00      inference(splitting,
% 0.99/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.99/1.00                [c_533]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_588,plain,
% 0.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sP0_iProver_split != iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_590,plain,
% 0.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sP0_iProver_split != iProver_top ),
% 0.99/1.00      inference(instantiation,[status(thm)],[c_588]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_541,plain,
% 0.99/1.00      ( sP2_iProver_split | sP0_iProver_split ),
% 0.99/1.00      inference(splitting,
% 0.99/1.00                [splitting(split),new_symbols(definition,[])],
% 0.99/1.00                [c_532]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_591,plain,
% 0.99/1.00      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_592,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47) != iProver_top
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0_47) = iProver_top
% 0.99/1.00      | sP2_iProver_split != iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_559,plain,
% 0.99/1.00      ( X0_52 != X1_52 | k1_zfmisc_1(X0_52) = k1_zfmisc_1(X1_52) ),
% 0.99/1.00      theory(equality) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_867,plain,
% 0.99/1.00      ( k2_zfmisc_1(X0_47,X0_48) != k2_zfmisc_1(sK1,sK2)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(instantiation,[status(thm)],[c_559]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_868,plain,
% 0.99/1.00      ( k2_zfmisc_1(sK1,sK2) != k2_zfmisc_1(sK1,sK2)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(instantiation,[status(thm)],[c_867]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1044,plain,
% 0.99/1.00      ( r1_tarski(k1_relat_1(sK4),X0_47) = iProver_top
% 0.99/1.00      | v4_relat_1(sK4,X0_47) != iProver_top ),
% 0.99/1.00      inference(global_propositional_subsumption,
% 0.99/1.00                [status(thm)],
% 0.99/1.00                [c_779,c_567,c_574,c_590,c_591,c_592,c_868]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1045,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47) != iProver_top
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0_47) = iProver_top ),
% 0.99/1.00      inference(renaming,[status(thm)],[c_1044]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_9,negated_conjecture,
% 0.99/1.00      ( r1_tarski(sK1,sK3) ),
% 0.99/1.00      inference(cnf_transformation,[],[f41]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_535,negated_conjecture,
% 0.99/1.00      ( r1_tarski(sK1,sK3) ),
% 0.99/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_773,plain,
% 0.99/1.00      ( r1_tarski(sK1,sK3) = iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_0,plain,
% 0.99/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 0.99/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_536,plain,
% 0.99/1.00      ( ~ r1_tarski(X0_47,X1_47)
% 0.99/1.00      | ~ r1_tarski(X2_47,X0_47)
% 0.99/1.00      | r1_tarski(X2_47,X1_47) ),
% 0.99/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_772,plain,
% 0.99/1.00      ( r1_tarski(X0_47,X1_47) != iProver_top
% 0.99/1.00      | r1_tarski(X2_47,X0_47) != iProver_top
% 0.99/1.00      | r1_tarski(X2_47,X1_47) = iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_948,plain,
% 0.99/1.00      ( r1_tarski(X0_47,sK3) = iProver_top
% 0.99/1.00      | r1_tarski(X0_47,sK1) != iProver_top ),
% 0.99/1.00      inference(superposition,[status(thm)],[c_773,c_772]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1053,plain,
% 0.99/1.00      ( v4_relat_1(sK4,sK1) != iProver_top
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
% 0.99/1.00      inference(superposition,[status(thm)],[c_1045,c_948]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_5,plain,
% 0.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 0.99/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_256,plain,
% 0.99/1.00      ( v4_relat_1(X0,X1)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sK4 != X0 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_257,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(unflattening,[status(thm)],[c_256]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_534,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(subtyping,[status(esa)],[c_257]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_774,plain,
% 0.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | v4_relat_1(sK4,X0_47) = iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_865,plain,
% 0.99/1.00      ( v4_relat_1(sK4,sK1) = iProver_top ),
% 0.99/1.00      inference(equality_resolution,[status(thm)],[c_774]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1131,plain,
% 0.99/1.00      ( r1_tarski(k1_relat_1(sK4),sK3) = iProver_top ),
% 0.99/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1053,c_865]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1,plain,
% 0.99/1.00      ( v4_relat_1(X0,X1) | ~ r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 0.99/1.00      inference(cnf_transformation,[],[f32]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_351,plain,
% 0.99/1.00      ( v4_relat_1(X0,X1)
% 0.99/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sK4 != X0 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_269]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_352,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0)
% 0.99/1.00      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(unflattening,[status(thm)],[c_351]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_531,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47)
% 0.99/1.00      | ~ r1_tarski(k1_relat_1(sK4),X0_47)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(subtyping,[status(esa)],[c_352]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_542,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47)
% 0.99/1.00      | ~ r1_tarski(k1_relat_1(sK4),X0_47)
% 0.99/1.00      | ~ sP3_iProver_split ),
% 0.99/1.00      inference(splitting,
% 0.99/1.00                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 0.99/1.00                [c_531]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_782,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47) = iProver_top
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0_47) != iProver_top
% 0.99/1.00      | sP3_iProver_split != iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_543,plain,
% 0.99/1.00      ( sP3_iProver_split | sP0_iProver_split ),
% 0.99/1.00      inference(splitting,
% 0.99/1.00                [splitting(split),new_symbols(definition,[])],
% 0.99/1.00                [c_531]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_596,plain,
% 0.99/1.00      ( sP3_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_597,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47) = iProver_top
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0_47) != iProver_top
% 0.99/1.00      | sP3_iProver_split != iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1139,plain,
% 0.99/1.00      ( r1_tarski(k1_relat_1(sK4),X0_47) != iProver_top
% 0.99/1.00      | v4_relat_1(sK4,X0_47) = iProver_top ),
% 0.99/1.00      inference(global_propositional_subsumption,
% 0.99/1.00                [status(thm)],
% 0.99/1.00                [c_782,c_567,c_574,c_590,c_596,c_597,c_868]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1140,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47) = iProver_top
% 0.99/1.00      | r1_tarski(k1_relat_1(sK4),X0_47) != iProver_top ),
% 0.99/1.00      inference(renaming,[status(thm)],[c_1139]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1146,plain,
% 0.99/1.00      ( v4_relat_1(sK4,sK3) = iProver_top ),
% 0.99/1.00      inference(superposition,[status(thm)],[c_1131,c_1140]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_538,plain,
% 0.99/1.00      ( ~ v4_relat_1(sK4,X0_47)
% 0.99/1.00      | k7_relat_1(sK4,X0_47) = sK4
% 0.99/1.00      | ~ sP1_iProver_split ),
% 0.99/1.00      inference(splitting,
% 0.99/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 0.99/1.00                [c_533]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_776,plain,
% 0.99/1.00      ( k7_relat_1(sK4,X0_47) = sK4
% 0.99/1.00      | v4_relat_1(sK4,X0_47) != iProver_top
% 0.99/1.00      | sP1_iProver_split != iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_539,plain,
% 0.99/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 0.99/1.00      inference(splitting,
% 0.99/1.00                [splitting(split),new_symbols(definition,[])],
% 0.99/1.00                [c_533]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_584,plain,
% 0.99/1.00      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_585,plain,
% 0.99/1.00      ( k7_relat_1(sK4,X0_47) = sK4
% 0.99/1.00      | v4_relat_1(sK4,X0_47) != iProver_top
% 0.99/1.00      | sP1_iProver_split != iProver_top ),
% 0.99/1.00      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_914,plain,
% 0.99/1.00      ( v4_relat_1(sK4,X0_47) != iProver_top | k7_relat_1(sK4,X0_47) = sK4 ),
% 0.99/1.00      inference(global_propositional_subsumption,
% 0.99/1.00                [status(thm)],
% 0.99/1.00                [c_776,c_567,c_574,c_584,c_585,c_590,c_868]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_915,plain,
% 0.99/1.00      ( k7_relat_1(sK4,X0_47) = sK4 | v4_relat_1(sK4,X0_47) != iProver_top ),
% 0.99/1.00      inference(renaming,[status(thm)],[c_914]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1284,plain,
% 0.99/1.00      ( k7_relat_1(sK4,sK3) = sK4 ),
% 0.99/1.00      inference(superposition,[status(thm)],[c_1146,c_915]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_6,plain,
% 0.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/1.00      | ~ v1_funct_1(X0)
% 0.99/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 0.99/1.00      inference(cnf_transformation,[],[f36]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_12,negated_conjecture,
% 0.99/1.00      ( v1_funct_1(sK4) ),
% 0.99/1.00      inference(cnf_transformation,[],[f38]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_197,plain,
% 0.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 0.99/1.00      | sK4 != X0 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_198,plain,
% 0.99/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.99/1.00      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 0.99/1.00      inference(unflattening,[status(thm)],[c_197]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_296,plain,
% 0.99/1.00      ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sK4 != sK4 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_198]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_438,plain,
% 0.99/1.00      ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 0.99/1.00      inference(equality_resolution_simp,[status(thm)],[c_296]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_530,plain,
% 0.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_48)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | k2_partfun1(X0_47,X0_48,sK4,X1_47) = k7_relat_1(sK4,X1_47) ),
% 0.99/1.00      inference(subtyping,[status(esa)],[c_438]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_879,plain,
% 0.99/1.00      ( k2_partfun1(sK1,sK2,sK4,X0_47) = k7_relat_1(sK4,X0_47) ),
% 0.99/1.00      inference(equality_resolution,[status(thm)],[c_530]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_11,negated_conjecture,
% 0.99/1.00      ( v1_funct_2(sK4,sK1,sK2) ),
% 0.99/1.00      inference(cnf_transformation,[],[f39]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_7,plain,
% 0.99/1.00      ( r2_relset_1(X0,X1,X2,X3)
% 0.99/1.00      | ~ v1_funct_2(X3,X0,X1)
% 0.99/1.00      | ~ v1_funct_2(X2,X0,X1)
% 0.99/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.99/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.99/1.00      | ~ v1_funct_1(X2)
% 0.99/1.00      | ~ v1_funct_1(X3)
% 0.99/1.00      | k1_funct_1(X3,sK0(X2,X3)) != k1_funct_1(X2,sK0(X2,X3)) ),
% 0.99/1.00      inference(cnf_transformation,[],[f37]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_8,negated_conjecture,
% 0.99/1.00      ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
% 0.99/1.00      inference(cnf_transformation,[],[f42]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_145,plain,
% 0.99/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 0.99/1.00      | ~ v1_funct_2(X3,X1,X2)
% 0.99/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/1.00      | ~ v1_funct_1(X0)
% 0.99/1.00      | ~ v1_funct_1(X3)
% 0.99/1.00      | k2_partfun1(sK1,sK2,sK4,sK3) != X3
% 0.99/1.00      | k1_funct_1(X3,sK0(X3,X0)) != k1_funct_1(X0,sK0(X3,X0))
% 0.99/1.00      | sK4 != X0
% 0.99/1.00      | sK2 != X2
% 0.99/1.00      | sK1 != X1 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_146,plain,
% 0.99/1.00      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 0.99/1.00      | ~ v1_funct_2(sK4,sK1,sK2)
% 0.99/1.00      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.99/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.99/1.00      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 0.99/1.00      | ~ v1_funct_1(sK4)
% 0.99/1.00      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 0.99/1.00      inference(unflattening,[status(thm)],[c_145]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_148,plain,
% 0.99/1.00      ( ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 0.99/1.00      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 0.99/1.00      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.99/1.00      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 0.99/1.00      inference(global_propositional_subsumption,
% 0.99/1.00                [status(thm)],
% 0.99/1.00                [c_146,c_12,c_11,c_10]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_149,plain,
% 0.99/1.00      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 0.99/1.00      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.99/1.00      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 0.99/1.00      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 0.99/1.00      inference(renaming,[status(thm)],[c_148]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_209,plain,
% 0.99/1.00      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 0.99/1.00      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.99/1.00      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 0.99/1.00      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_149]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_232,plain,
% 0.99/1.00      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 0.99/1.00      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 0.99/1.00      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 0.99/1.00      | sK2 != sK2
% 0.99/1.00      | sK1 != sK1 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_209]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_280,plain,
% 0.99/1.00      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 0.99/1.00      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 0.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 0.99/1.00      | sK2 != sK2
% 0.99/1.00      | sK1 != sK1 ),
% 0.99/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_232]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_440,plain,
% 0.99/1.00      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 0.99/1.00      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 0.99/1.00      inference(equality_resolution_simp,[status(thm)],[c_280]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_529,plain,
% 0.99/1.00      ( k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 0.99/1.00      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4 ),
% 0.99/1.00      inference(subtyping,[status(esa)],[c_440]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_896,plain,
% 0.99/1.00      ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
% 0.99/1.00      | k7_relat_1(sK4,sK3) != sK4 ),
% 0.99/1.00      inference(demodulation,[status(thm)],[c_879,c_529]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1286,plain,
% 0.99/1.00      ( k1_funct_1(sK4,sK0(sK4,sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
% 0.99/1.00      | sK4 != sK4 ),
% 0.99/1.00      inference(demodulation,[status(thm)],[c_1284,c_896]) ).
% 0.99/1.00  
% 0.99/1.00  cnf(c_1338,plain,
% 0.99/1.00      ( $false ),
% 0.99/1.00      inference(equality_resolution_simp,[status(thm)],[c_1286]) ).
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.99/1.00  
% 0.99/1.00  ------                               Statistics
% 0.99/1.00  
% 0.99/1.00  ------ General
% 0.99/1.00  
% 0.99/1.00  abstr_ref_over_cycles:                  0
% 0.99/1.00  abstr_ref_under_cycles:                 0
% 0.99/1.00  gc_basic_clause_elim:                   0
% 0.99/1.00  forced_gc_time:                         0
% 0.99/1.00  parsing_time:                           0.009
% 0.99/1.00  unif_index_cands_time:                  0.
% 0.99/1.00  unif_index_add_time:                    0.
% 0.99/1.00  orderings_time:                         0.
% 0.99/1.00  out_proof_time:                         0.011
% 0.99/1.00  total_time:                             0.077
% 0.99/1.00  num_of_symbols:                         57
% 0.99/1.00  num_of_terms:                           1185
% 0.99/1.00  
% 0.99/1.00  ------ Preprocessing
% 0.99/1.00  
% 0.99/1.00  num_of_splits:                          6
% 0.99/1.00  num_of_split_atoms:                     4
% 0.99/1.00  num_of_reused_defs:                     2
% 0.99/1.00  num_eq_ax_congr_red:                    15
% 0.99/1.00  num_of_sem_filtered_clauses:            1
% 0.99/1.00  num_of_subtypes:                        7
% 0.99/1.00  monotx_restored_types:                  0
% 0.99/1.00  sat_num_of_epr_types:                   0
% 0.99/1.00  sat_num_of_non_cyclic_types:            0
% 0.99/1.00  sat_guarded_non_collapsed_types:        0
% 0.99/1.00  num_pure_diseq_elim:                    0
% 0.99/1.00  simp_replaced_by:                       0
% 0.99/1.00  res_preprocessed:                       82
% 0.99/1.00  prep_upred:                             0
% 0.99/1.00  prep_unflattend:                        10
% 0.99/1.00  smt_new_axioms:                         0
% 0.99/1.00  pred_elim_cands:                        2
% 0.99/1.00  pred_elim:                              5
% 0.99/1.00  pred_elim_cl:                           5
% 0.99/1.00  pred_elim_cycles:                       8
% 0.99/1.00  merged_defs:                            0
% 0.99/1.00  merged_defs_ncl:                        0
% 0.99/1.00  bin_hyper_res:                          0
% 0.99/1.00  prep_cycles:                            4
% 0.99/1.00  pred_elim_time:                         0.007
% 0.99/1.00  splitting_time:                         0.
% 0.99/1.00  sem_filter_time:                        0.
% 0.99/1.00  monotx_time:                            0.
% 0.99/1.00  subtype_inf_time:                       0.
% 0.99/1.00  
% 0.99/1.00  ------ Problem properties
% 0.99/1.00  
% 0.99/1.00  clauses:                                14
% 0.99/1.00  conjectures:                            1
% 0.99/1.00  epr:                                    5
% 0.99/1.00  horn:                                   11
% 0.99/1.00  ground:                                 5
% 0.99/1.00  unary:                                  1
% 0.99/1.00  binary:                                 9
% 0.99/1.00  lits:                                   31
% 0.99/1.00  lits_eq:                                9
% 0.99/1.00  fd_pure:                                0
% 0.99/1.00  fd_pseudo:                              0
% 0.99/1.00  fd_cond:                                0
% 0.99/1.00  fd_pseudo_cond:                         0
% 0.99/1.00  ac_symbols:                             0
% 0.99/1.00  
% 0.99/1.00  ------ Propositional Solver
% 0.99/1.00  
% 0.99/1.00  prop_solver_calls:                      28
% 0.99/1.00  prop_fast_solver_calls:                 505
% 0.99/1.00  smt_solver_calls:                       0
% 0.99/1.00  smt_fast_solver_calls:                  0
% 0.99/1.00  prop_num_of_clauses:                    360
% 0.99/1.00  prop_preprocess_simplified:             2219
% 0.99/1.00  prop_fo_subsumed:                       13
% 0.99/1.00  prop_solver_time:                       0.
% 0.99/1.00  smt_solver_time:                        0.
% 0.99/1.00  smt_fast_solver_time:                   0.
% 0.99/1.00  prop_fast_solver_time:                  0.
% 0.99/1.00  prop_unsat_core_time:                   0.
% 0.99/1.00  
% 0.99/1.00  ------ QBF
% 0.99/1.00  
% 0.99/1.00  qbf_q_res:                              0
% 0.99/1.00  qbf_num_tautologies:                    0
% 0.99/1.00  qbf_prep_cycles:                        0
% 0.99/1.00  
% 0.99/1.00  ------ BMC1
% 0.99/1.00  
% 0.99/1.00  bmc1_current_bound:                     -1
% 0.99/1.00  bmc1_last_solved_bound:                 -1
% 0.99/1.00  bmc1_unsat_core_size:                   -1
% 0.99/1.00  bmc1_unsat_core_parents_size:           -1
% 0.99/1.00  bmc1_merge_next_fun:                    0
% 0.99/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.99/1.00  
% 0.99/1.00  ------ Instantiation
% 0.99/1.00  
% 0.99/1.00  inst_num_of_clauses:                    134
% 0.99/1.00  inst_num_in_passive:                    42
% 0.99/1.00  inst_num_in_active:                     85
% 0.99/1.00  inst_num_in_unprocessed:                7
% 0.99/1.00  inst_num_of_loops:                      120
% 0.99/1.00  inst_num_of_learning_restarts:          0
% 0.99/1.00  inst_num_moves_active_passive:          31
% 0.99/1.00  inst_lit_activity:                      0
% 0.99/1.00  inst_lit_activity_moves:                0
% 0.99/1.00  inst_num_tautologies:                   0
% 0.99/1.00  inst_num_prop_implied:                  0
% 0.99/1.00  inst_num_existing_simplified:           0
% 0.99/1.00  inst_num_eq_res_simplified:             0
% 0.99/1.00  inst_num_child_elim:                    0
% 0.99/1.00  inst_num_of_dismatching_blockings:      9
% 0.99/1.00  inst_num_of_non_proper_insts:           85
% 0.99/1.00  inst_num_of_duplicates:                 0
% 0.99/1.00  inst_inst_num_from_inst_to_res:         0
% 0.99/1.00  inst_dismatching_checking_time:         0.
% 0.99/1.00  
% 0.99/1.00  ------ Resolution
% 0.99/1.00  
% 0.99/1.00  res_num_of_clauses:                     0
% 0.99/1.00  res_num_in_passive:                     0
% 0.99/1.00  res_num_in_active:                      0
% 0.99/1.00  res_num_of_loops:                       86
% 0.99/1.00  res_forward_subset_subsumed:            11
% 0.99/1.00  res_backward_subset_subsumed:           0
% 0.99/1.00  res_forward_subsumed:                   0
% 0.99/1.00  res_backward_subsumed:                  0
% 0.99/1.00  res_forward_subsumption_resolution:     0
% 0.99/1.00  res_backward_subsumption_resolution:    0
% 0.99/1.00  res_clause_to_clause_subsumption:       27
% 0.99/1.00  res_orphan_elimination:                 0
% 0.99/1.00  res_tautology_del:                      20
% 0.99/1.00  res_num_eq_res_simplified:              2
% 0.99/1.00  res_num_sel_changes:                    0
% 0.99/1.00  res_moves_from_active_to_pass:          0
% 0.99/1.00  
% 0.99/1.00  ------ Superposition
% 0.99/1.00  
% 0.99/1.00  sup_time_total:                         0.
% 0.99/1.00  sup_time_generating:                    0.
% 0.99/1.00  sup_time_sim_full:                      0.
% 0.99/1.00  sup_time_sim_immed:                     0.
% 0.99/1.00  
% 0.99/1.00  sup_num_of_clauses:                     21
% 0.99/1.00  sup_num_in_active:                      20
% 0.99/1.00  sup_num_in_passive:                     1
% 0.99/1.00  sup_num_of_loops:                       22
% 0.99/1.00  sup_fw_superposition:                   6
% 0.99/1.00  sup_bw_superposition:                   4
% 0.99/1.00  sup_immediate_simplified:               2
% 0.99/1.00  sup_given_eliminated:                   0
% 0.99/1.00  comparisons_done:                       0
% 0.99/1.00  comparisons_avoided:                    0
% 0.99/1.00  
% 0.99/1.00  ------ Simplifications
% 0.99/1.00  
% 0.99/1.00  
% 0.99/1.00  sim_fw_subset_subsumed:                 1
% 0.99/1.00  sim_bw_subset_subsumed:                 0
% 0.99/1.00  sim_fw_subsumed:                        1
% 0.99/1.00  sim_bw_subsumed:                        0
% 0.99/1.00  sim_fw_subsumption_res:                 0
% 0.99/1.00  sim_bw_subsumption_res:                 0
% 0.99/1.00  sim_tautology_del:                      1
% 0.99/1.00  sim_eq_tautology_del:                   0
% 0.99/1.00  sim_eq_res_simp:                        0
% 0.99/1.00  sim_fw_demodulated:                     0
% 0.99/1.00  sim_bw_demodulated:                     2
% 0.99/1.00  sim_light_normalised:                   0
% 0.99/1.00  sim_joinable_taut:                      0
% 0.99/1.00  sim_joinable_simp:                      0
% 0.99/1.00  sim_ac_normalised:                      0
% 0.99/1.00  sim_smt_subsumption:                    0
% 0.99/1.00  
%------------------------------------------------------------------------------
