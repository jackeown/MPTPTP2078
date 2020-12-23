%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:05 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 434 expanded)
%              Number of clauses        :   77 ( 168 expanded)
%              Number of leaves         :   12 (  79 expanded)
%              Depth                    :   23
%              Number of atoms          :  357 (1554 expanded)
%              Number of equality atoms :  134 ( 221 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

fof(f43,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
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

fof(f39,plain,(
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

fof(f44,plain,(
    ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_800,plain,
    ( r1_tarski(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_271,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_272,plain,
    ( v4_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_799,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | v4_relat_1(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_888,plain,
    ( v4_relat_1(sK4,sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_799])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_283,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_284,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_351,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_284])).

cnf(c_352,plain,
    ( ~ v4_relat_1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_555,plain,
    ( ~ v4_relat_1(sK4,X0)
    | r1_tarski(k1_relat_1(sK4),X0)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_352])).

cnf(c_794,plain,
    ( v4_relat_1(sK4,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_556,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_352])).

cnf(c_589,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_590,plain,
    ( v4_relat_1(sK4,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_560,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_900,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_2,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_366,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_284])).

cnf(c_367,plain,
    ( v4_relat_1(sK4,X0)
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_552,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_367])).

cnf(c_902,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_906,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_1215,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | v4_relat_1(sK4,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_794,c_589,c_590,c_900,c_906])).

cnf(c_1216,plain,
    ( v4_relat_1(sK4,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1215])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_801,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1223,plain,
    ( k2_xboole_0(k1_relat_1(sK4),X0) = X0
    | v4_relat_1(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_801])).

cnf(c_1435,plain,
    ( k2_xboole_0(k1_relat_1(sK4),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_888,c_1223])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_802,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1535,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1435,c_802])).

cnf(c_553,plain,
    ( v4_relat_1(sK4,X0)
    | ~ r1_tarski(k1_relat_1(sK4),X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_367])).

cnf(c_791,plain,
    ( v4_relat_1(sK4,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_554,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_367])).

cnf(c_582,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_583,plain,
    ( v4_relat_1(sK4,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_1057,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | v4_relat_1(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_791,c_582,c_583,c_900,c_906])).

cnf(c_1058,plain,
    ( v4_relat_1(sK4,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1057])).

cnf(c_1543,plain,
    ( v4_relat_1(sK4,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1058])).

cnf(c_1731,plain,
    ( v4_relat_1(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_1543])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_336,plain,
    ( ~ v4_relat_1(X0,X1)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_284])).

cnf(c_337,plain,
    ( ~ v4_relat_1(sK4,X0)
    | k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_557,plain,
    ( ~ v4_relat_1(sK4,X0)
    | k7_relat_1(sK4,X0) = sK4
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_337])).

cnf(c_797,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | v4_relat_1(sK4,X0) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_558,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_337])).

cnf(c_594,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_595,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | v4_relat_1(sK4,X0) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_976,plain,
    ( v4_relat_1(sK4,X0) != iProver_top
    | k7_relat_1(sK4,X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_797,c_594,c_595,c_900,c_906])).

cnf(c_977,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | v4_relat_1(sK4,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_976])).

cnf(c_1736,plain,
    ( k7_relat_1(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_1731,c_977])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_212,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_213,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_311,plain,
    ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_213])).

cnf(c_454,plain,
    ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_311])).

cnf(c_915,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_454])).

cnf(c_12,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X2,X3)) != k1_funct_1(X2,sK0(X2,X3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_160,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_161,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_163,plain,
    ( ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_161,c_13,c_12,c_11])).

cnf(c_164,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_224,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_164])).

cnf(c_247,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_224])).

cnf(c_295,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK2 != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_247])).

cnf(c_456,plain,
    ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
    | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_295])).

cnf(c_946,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
    | k7_relat_1(sK4,sK3) != sK4 ),
    inference(demodulation,[status(thm)],[c_915,c_456])).

cnf(c_1778,plain,
    ( k1_funct_1(sK4,sK0(sK4,sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_1736,c_946])).

cnf(c_1858,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1778])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.60/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.01  
% 1.60/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.60/1.01  
% 1.60/1.01  ------  iProver source info
% 1.60/1.01  
% 1.60/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.60/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.60/1.01  git: non_committed_changes: false
% 1.60/1.01  git: last_make_outside_of_git: false
% 1.60/1.01  
% 1.60/1.01  ------ 
% 1.60/1.01  
% 1.60/1.01  ------ Input Options
% 1.60/1.01  
% 1.60/1.01  --out_options                           all
% 1.60/1.01  --tptp_safe_out                         true
% 1.60/1.01  --problem_path                          ""
% 1.60/1.01  --include_path                          ""
% 1.60/1.01  --clausifier                            res/vclausify_rel
% 1.60/1.01  --clausifier_options                    --mode clausify
% 1.60/1.01  --stdin                                 false
% 1.60/1.01  --stats_out                             all
% 1.60/1.01  
% 1.60/1.01  ------ General Options
% 1.60/1.01  
% 1.60/1.01  --fof                                   false
% 1.60/1.01  --time_out_real                         305.
% 1.60/1.01  --time_out_virtual                      -1.
% 1.60/1.01  --symbol_type_check                     false
% 1.60/1.01  --clausify_out                          false
% 1.60/1.01  --sig_cnt_out                           false
% 1.60/1.01  --trig_cnt_out                          false
% 1.60/1.01  --trig_cnt_out_tolerance                1.
% 1.60/1.01  --trig_cnt_out_sk_spl                   false
% 1.60/1.01  --abstr_cl_out                          false
% 1.60/1.01  
% 1.60/1.01  ------ Global Options
% 1.60/1.01  
% 1.60/1.01  --schedule                              default
% 1.60/1.01  --add_important_lit                     false
% 1.60/1.01  --prop_solver_per_cl                    1000
% 1.60/1.01  --min_unsat_core                        false
% 1.60/1.01  --soft_assumptions                      false
% 1.60/1.01  --soft_lemma_size                       3
% 1.60/1.01  --prop_impl_unit_size                   0
% 1.60/1.01  --prop_impl_unit                        []
% 1.60/1.01  --share_sel_clauses                     true
% 1.60/1.01  --reset_solvers                         false
% 1.60/1.01  --bc_imp_inh                            [conj_cone]
% 1.60/1.01  --conj_cone_tolerance                   3.
% 1.60/1.01  --extra_neg_conj                        none
% 1.60/1.01  --large_theory_mode                     true
% 1.60/1.01  --prolific_symb_bound                   200
% 1.60/1.01  --lt_threshold                          2000
% 1.60/1.01  --clause_weak_htbl                      true
% 1.60/1.01  --gc_record_bc_elim                     false
% 1.60/1.01  
% 1.60/1.01  ------ Preprocessing Options
% 1.60/1.01  
% 1.60/1.01  --preprocessing_flag                    true
% 1.60/1.01  --time_out_prep_mult                    0.1
% 1.60/1.01  --splitting_mode                        input
% 1.60/1.01  --splitting_grd                         true
% 1.60/1.01  --splitting_cvd                         false
% 1.60/1.01  --splitting_cvd_svl                     false
% 1.60/1.01  --splitting_nvd                         32
% 1.60/1.01  --sub_typing                            true
% 1.60/1.01  --prep_gs_sim                           true
% 1.60/1.01  --prep_unflatten                        true
% 1.60/1.01  --prep_res_sim                          true
% 1.60/1.01  --prep_upred                            true
% 1.60/1.01  --prep_sem_filter                       exhaustive
% 1.60/1.01  --prep_sem_filter_out                   false
% 1.60/1.01  --pred_elim                             true
% 1.60/1.01  --res_sim_input                         true
% 1.60/1.01  --eq_ax_congr_red                       true
% 1.60/1.01  --pure_diseq_elim                       true
% 1.60/1.01  --brand_transform                       false
% 1.60/1.01  --non_eq_to_eq                          false
% 1.60/1.01  --prep_def_merge                        true
% 1.60/1.01  --prep_def_merge_prop_impl              false
% 1.60/1.01  --prep_def_merge_mbd                    true
% 1.60/1.01  --prep_def_merge_tr_red                 false
% 1.60/1.01  --prep_def_merge_tr_cl                  false
% 1.60/1.01  --smt_preprocessing                     true
% 1.60/1.01  --smt_ac_axioms                         fast
% 1.60/1.01  --preprocessed_out                      false
% 1.60/1.01  --preprocessed_stats                    false
% 1.60/1.01  
% 1.60/1.01  ------ Abstraction refinement Options
% 1.60/1.01  
% 1.60/1.01  --abstr_ref                             []
% 1.60/1.01  --abstr_ref_prep                        false
% 1.60/1.01  --abstr_ref_until_sat                   false
% 1.60/1.01  --abstr_ref_sig_restrict                funpre
% 1.60/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.60/1.01  --abstr_ref_under                       []
% 1.60/1.01  
% 1.60/1.01  ------ SAT Options
% 1.60/1.01  
% 1.60/1.01  --sat_mode                              false
% 1.60/1.01  --sat_fm_restart_options                ""
% 1.60/1.01  --sat_gr_def                            false
% 1.60/1.01  --sat_epr_types                         true
% 1.60/1.01  --sat_non_cyclic_types                  false
% 1.60/1.01  --sat_finite_models                     false
% 1.60/1.01  --sat_fm_lemmas                         false
% 1.60/1.01  --sat_fm_prep                           false
% 1.60/1.01  --sat_fm_uc_incr                        true
% 1.60/1.01  --sat_out_model                         small
% 1.60/1.01  --sat_out_clauses                       false
% 1.60/1.01  
% 1.60/1.01  ------ QBF Options
% 1.60/1.01  
% 1.60/1.01  --qbf_mode                              false
% 1.60/1.01  --qbf_elim_univ                         false
% 1.60/1.01  --qbf_dom_inst                          none
% 1.60/1.01  --qbf_dom_pre_inst                      false
% 1.60/1.01  --qbf_sk_in                             false
% 1.60/1.01  --qbf_pred_elim                         true
% 1.60/1.01  --qbf_split                             512
% 1.60/1.01  
% 1.60/1.01  ------ BMC1 Options
% 1.60/1.01  
% 1.60/1.01  --bmc1_incremental                      false
% 1.60/1.01  --bmc1_axioms                           reachable_all
% 1.60/1.01  --bmc1_min_bound                        0
% 1.60/1.01  --bmc1_max_bound                        -1
% 1.60/1.01  --bmc1_max_bound_default                -1
% 1.60/1.01  --bmc1_symbol_reachability              true
% 1.60/1.01  --bmc1_property_lemmas                  false
% 1.60/1.01  --bmc1_k_induction                      false
% 1.60/1.01  --bmc1_non_equiv_states                 false
% 1.60/1.01  --bmc1_deadlock                         false
% 1.60/1.01  --bmc1_ucm                              false
% 1.60/1.01  --bmc1_add_unsat_core                   none
% 1.60/1.01  --bmc1_unsat_core_children              false
% 1.60/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.60/1.01  --bmc1_out_stat                         full
% 1.60/1.01  --bmc1_ground_init                      false
% 1.60/1.01  --bmc1_pre_inst_next_state              false
% 1.60/1.01  --bmc1_pre_inst_state                   false
% 1.60/1.01  --bmc1_pre_inst_reach_state             false
% 1.60/1.01  --bmc1_out_unsat_core                   false
% 1.60/1.01  --bmc1_aig_witness_out                  false
% 1.60/1.01  --bmc1_verbose                          false
% 1.60/1.01  --bmc1_dump_clauses_tptp                false
% 1.60/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.60/1.01  --bmc1_dump_file                        -
% 1.60/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.60/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.60/1.01  --bmc1_ucm_extend_mode                  1
% 1.60/1.01  --bmc1_ucm_init_mode                    2
% 1.60/1.01  --bmc1_ucm_cone_mode                    none
% 1.60/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.60/1.01  --bmc1_ucm_relax_model                  4
% 1.60/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.60/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.60/1.01  --bmc1_ucm_layered_model                none
% 1.60/1.01  --bmc1_ucm_max_lemma_size               10
% 1.60/1.01  
% 1.60/1.01  ------ AIG Options
% 1.60/1.01  
% 1.60/1.01  --aig_mode                              false
% 1.60/1.01  
% 1.60/1.01  ------ Instantiation Options
% 1.60/1.01  
% 1.60/1.01  --instantiation_flag                    true
% 1.60/1.01  --inst_sos_flag                         false
% 1.60/1.01  --inst_sos_phase                        true
% 1.60/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.60/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.60/1.01  --inst_lit_sel_side                     num_symb
% 1.60/1.01  --inst_solver_per_active                1400
% 1.60/1.01  --inst_solver_calls_frac                1.
% 1.60/1.01  --inst_passive_queue_type               priority_queues
% 1.60/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.60/1.01  --inst_passive_queues_freq              [25;2]
% 1.60/1.01  --inst_dismatching                      true
% 1.60/1.01  --inst_eager_unprocessed_to_passive     true
% 1.60/1.01  --inst_prop_sim_given                   true
% 1.60/1.01  --inst_prop_sim_new                     false
% 1.60/1.01  --inst_subs_new                         false
% 1.60/1.01  --inst_eq_res_simp                      false
% 1.60/1.01  --inst_subs_given                       false
% 1.60/1.01  --inst_orphan_elimination               true
% 1.60/1.01  --inst_learning_loop_flag               true
% 1.60/1.01  --inst_learning_start                   3000
% 1.60/1.01  --inst_learning_factor                  2
% 1.60/1.01  --inst_start_prop_sim_after_learn       3
% 1.60/1.01  --inst_sel_renew                        solver
% 1.60/1.01  --inst_lit_activity_flag                true
% 1.60/1.01  --inst_restr_to_given                   false
% 1.60/1.01  --inst_activity_threshold               500
% 1.60/1.01  --inst_out_proof                        true
% 1.60/1.01  
% 1.60/1.01  ------ Resolution Options
% 1.60/1.01  
% 1.60/1.01  --resolution_flag                       true
% 1.60/1.01  --res_lit_sel                           adaptive
% 1.60/1.01  --res_lit_sel_side                      none
% 1.60/1.01  --res_ordering                          kbo
% 1.60/1.01  --res_to_prop_solver                    active
% 1.60/1.01  --res_prop_simpl_new                    false
% 1.60/1.01  --res_prop_simpl_given                  true
% 1.60/1.01  --res_passive_queue_type                priority_queues
% 1.60/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.60/1.01  --res_passive_queues_freq               [15;5]
% 1.60/1.01  --res_forward_subs                      full
% 1.60/1.01  --res_backward_subs                     full
% 1.60/1.01  --res_forward_subs_resolution           true
% 1.60/1.01  --res_backward_subs_resolution          true
% 1.60/1.01  --res_orphan_elimination                true
% 1.60/1.01  --res_time_limit                        2.
% 1.60/1.01  --res_out_proof                         true
% 1.60/1.01  
% 1.60/1.01  ------ Superposition Options
% 1.60/1.01  
% 1.60/1.01  --superposition_flag                    true
% 1.60/1.01  --sup_passive_queue_type                priority_queues
% 1.60/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.60/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.60/1.01  --demod_completeness_check              fast
% 1.60/1.01  --demod_use_ground                      true
% 1.60/1.01  --sup_to_prop_solver                    passive
% 1.60/1.01  --sup_prop_simpl_new                    true
% 1.60/1.01  --sup_prop_simpl_given                  true
% 1.60/1.01  --sup_fun_splitting                     false
% 1.60/1.01  --sup_smt_interval                      50000
% 1.60/1.01  
% 1.60/1.01  ------ Superposition Simplification Setup
% 1.60/1.01  
% 1.60/1.01  --sup_indices_passive                   []
% 1.60/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.60/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.60/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.60/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.60/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.60/1.01  --sup_full_bw                           [BwDemod]
% 1.60/1.01  --sup_immed_triv                        [TrivRules]
% 1.60/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.60/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.60/1.01  --sup_immed_bw_main                     []
% 1.60/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.60/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.60/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.60/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.60/1.01  
% 1.60/1.01  ------ Combination Options
% 1.60/1.01  
% 1.60/1.01  --comb_res_mult                         3
% 1.60/1.01  --comb_sup_mult                         2
% 1.60/1.01  --comb_inst_mult                        10
% 1.60/1.01  
% 1.60/1.01  ------ Debug Options
% 1.60/1.01  
% 1.60/1.01  --dbg_backtrace                         false
% 1.60/1.01  --dbg_dump_prop_clauses                 false
% 1.60/1.01  --dbg_dump_prop_clauses_file            -
% 1.60/1.01  --dbg_out_stat                          false
% 1.60/1.01  ------ Parsing...
% 1.60/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.60/1.01  
% 1.60/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.60/1.01  
% 1.60/1.01  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.60/1.01  
% 1.60/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.60/1.01  ------ Proving...
% 1.60/1.01  ------ Problem Properties 
% 1.60/1.01  
% 1.60/1.01  
% 1.60/1.01  clauses                                 15
% 1.60/1.01  conjectures                             1
% 1.60/1.01  EPR                                     4
% 1.60/1.01  Horn                                    12
% 1.60/1.01  unary                                   1
% 1.60/1.01  binary                                  11
% 1.60/1.01  lits                                    32
% 1.60/1.01  lits eq                                 10
% 1.60/1.01  fd_pure                                 0
% 1.60/1.01  fd_pseudo                               0
% 1.60/1.01  fd_cond                                 0
% 1.60/1.01  fd_pseudo_cond                          0
% 1.60/1.01  AC symbols                              0
% 1.60/1.01  
% 1.60/1.01  ------ Schedule dynamic 5 is on 
% 1.60/1.01  
% 1.60/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.60/1.01  
% 1.60/1.01  
% 1.60/1.01  ------ 
% 1.60/1.01  Current options:
% 1.60/1.01  ------ 
% 1.60/1.01  
% 1.60/1.01  ------ Input Options
% 1.60/1.01  
% 1.60/1.01  --out_options                           all
% 1.60/1.01  --tptp_safe_out                         true
% 1.60/1.01  --problem_path                          ""
% 1.60/1.01  --include_path                          ""
% 1.60/1.01  --clausifier                            res/vclausify_rel
% 1.60/1.01  --clausifier_options                    --mode clausify
% 1.60/1.01  --stdin                                 false
% 1.60/1.01  --stats_out                             all
% 1.60/1.01  
% 1.60/1.01  ------ General Options
% 1.60/1.01  
% 1.60/1.01  --fof                                   false
% 1.60/1.01  --time_out_real                         305.
% 1.60/1.01  --time_out_virtual                      -1.
% 1.60/1.01  --symbol_type_check                     false
% 1.60/1.01  --clausify_out                          false
% 1.60/1.01  --sig_cnt_out                           false
% 1.60/1.01  --trig_cnt_out                          false
% 1.60/1.01  --trig_cnt_out_tolerance                1.
% 1.60/1.01  --trig_cnt_out_sk_spl                   false
% 1.60/1.01  --abstr_cl_out                          false
% 1.60/1.01  
% 1.60/1.01  ------ Global Options
% 1.60/1.01  
% 1.60/1.01  --schedule                              default
% 1.60/1.01  --add_important_lit                     false
% 1.60/1.01  --prop_solver_per_cl                    1000
% 1.60/1.01  --min_unsat_core                        false
% 1.60/1.01  --soft_assumptions                      false
% 1.60/1.01  --soft_lemma_size                       3
% 1.60/1.01  --prop_impl_unit_size                   0
% 1.60/1.01  --prop_impl_unit                        []
% 1.60/1.01  --share_sel_clauses                     true
% 1.60/1.01  --reset_solvers                         false
% 1.60/1.01  --bc_imp_inh                            [conj_cone]
% 1.60/1.01  --conj_cone_tolerance                   3.
% 1.60/1.01  --extra_neg_conj                        none
% 1.60/1.01  --large_theory_mode                     true
% 1.60/1.01  --prolific_symb_bound                   200
% 1.60/1.01  --lt_threshold                          2000
% 1.60/1.01  --clause_weak_htbl                      true
% 1.60/1.01  --gc_record_bc_elim                     false
% 1.60/1.01  
% 1.60/1.01  ------ Preprocessing Options
% 1.60/1.01  
% 1.60/1.01  --preprocessing_flag                    true
% 1.60/1.01  --time_out_prep_mult                    0.1
% 1.60/1.01  --splitting_mode                        input
% 1.60/1.01  --splitting_grd                         true
% 1.60/1.01  --splitting_cvd                         false
% 1.60/1.01  --splitting_cvd_svl                     false
% 1.60/1.01  --splitting_nvd                         32
% 1.60/1.01  --sub_typing                            true
% 1.60/1.01  --prep_gs_sim                           true
% 1.60/1.01  --prep_unflatten                        true
% 1.60/1.01  --prep_res_sim                          true
% 1.60/1.01  --prep_upred                            true
% 1.60/1.01  --prep_sem_filter                       exhaustive
% 1.60/1.01  --prep_sem_filter_out                   false
% 1.60/1.01  --pred_elim                             true
% 1.60/1.01  --res_sim_input                         true
% 1.60/1.01  --eq_ax_congr_red                       true
% 1.60/1.01  --pure_diseq_elim                       true
% 1.60/1.01  --brand_transform                       false
% 1.60/1.01  --non_eq_to_eq                          false
% 1.60/1.01  --prep_def_merge                        true
% 1.60/1.01  --prep_def_merge_prop_impl              false
% 1.60/1.01  --prep_def_merge_mbd                    true
% 1.60/1.01  --prep_def_merge_tr_red                 false
% 1.60/1.01  --prep_def_merge_tr_cl                  false
% 1.60/1.01  --smt_preprocessing                     true
% 1.60/1.01  --smt_ac_axioms                         fast
% 1.60/1.01  --preprocessed_out                      false
% 1.60/1.01  --preprocessed_stats                    false
% 1.60/1.01  
% 1.60/1.01  ------ Abstraction refinement Options
% 1.60/1.01  
% 1.60/1.01  --abstr_ref                             []
% 1.60/1.01  --abstr_ref_prep                        false
% 1.60/1.01  --abstr_ref_until_sat                   false
% 1.60/1.01  --abstr_ref_sig_restrict                funpre
% 1.60/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.60/1.01  --abstr_ref_under                       []
% 1.60/1.01  
% 1.60/1.01  ------ SAT Options
% 1.60/1.01  
% 1.60/1.01  --sat_mode                              false
% 1.60/1.01  --sat_fm_restart_options                ""
% 1.60/1.01  --sat_gr_def                            false
% 1.60/1.01  --sat_epr_types                         true
% 1.60/1.01  --sat_non_cyclic_types                  false
% 1.60/1.01  --sat_finite_models                     false
% 1.60/1.01  --sat_fm_lemmas                         false
% 1.60/1.01  --sat_fm_prep                           false
% 1.60/1.01  --sat_fm_uc_incr                        true
% 1.60/1.01  --sat_out_model                         small
% 1.60/1.01  --sat_out_clauses                       false
% 1.60/1.01  
% 1.60/1.01  ------ QBF Options
% 1.60/1.01  
% 1.60/1.01  --qbf_mode                              false
% 1.60/1.01  --qbf_elim_univ                         false
% 1.60/1.01  --qbf_dom_inst                          none
% 1.60/1.01  --qbf_dom_pre_inst                      false
% 1.60/1.01  --qbf_sk_in                             false
% 1.60/1.01  --qbf_pred_elim                         true
% 1.60/1.01  --qbf_split                             512
% 1.60/1.01  
% 1.60/1.01  ------ BMC1 Options
% 1.60/1.01  
% 1.60/1.01  --bmc1_incremental                      false
% 1.60/1.01  --bmc1_axioms                           reachable_all
% 1.60/1.01  --bmc1_min_bound                        0
% 1.60/1.01  --bmc1_max_bound                        -1
% 1.60/1.01  --bmc1_max_bound_default                -1
% 1.60/1.01  --bmc1_symbol_reachability              true
% 1.60/1.01  --bmc1_property_lemmas                  false
% 1.60/1.01  --bmc1_k_induction                      false
% 1.60/1.01  --bmc1_non_equiv_states                 false
% 1.60/1.01  --bmc1_deadlock                         false
% 1.60/1.01  --bmc1_ucm                              false
% 1.60/1.01  --bmc1_add_unsat_core                   none
% 1.60/1.01  --bmc1_unsat_core_children              false
% 1.60/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.60/1.01  --bmc1_out_stat                         full
% 1.60/1.01  --bmc1_ground_init                      false
% 1.60/1.01  --bmc1_pre_inst_next_state              false
% 1.60/1.01  --bmc1_pre_inst_state                   false
% 1.60/1.01  --bmc1_pre_inst_reach_state             false
% 1.60/1.01  --bmc1_out_unsat_core                   false
% 1.60/1.01  --bmc1_aig_witness_out                  false
% 1.60/1.01  --bmc1_verbose                          false
% 1.60/1.01  --bmc1_dump_clauses_tptp                false
% 1.60/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.60/1.01  --bmc1_dump_file                        -
% 1.60/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.60/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.60/1.01  --bmc1_ucm_extend_mode                  1
% 1.60/1.01  --bmc1_ucm_init_mode                    2
% 1.60/1.01  --bmc1_ucm_cone_mode                    none
% 1.60/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.60/1.01  --bmc1_ucm_relax_model                  4
% 1.60/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.60/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.60/1.01  --bmc1_ucm_layered_model                none
% 1.60/1.01  --bmc1_ucm_max_lemma_size               10
% 1.60/1.01  
% 1.60/1.01  ------ AIG Options
% 1.60/1.01  
% 1.60/1.01  --aig_mode                              false
% 1.60/1.01  
% 1.60/1.01  ------ Instantiation Options
% 1.60/1.01  
% 1.60/1.01  --instantiation_flag                    true
% 1.60/1.01  --inst_sos_flag                         false
% 1.60/1.01  --inst_sos_phase                        true
% 1.60/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.60/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.60/1.01  --inst_lit_sel_side                     none
% 1.60/1.01  --inst_solver_per_active                1400
% 1.60/1.01  --inst_solver_calls_frac                1.
% 1.60/1.01  --inst_passive_queue_type               priority_queues
% 1.60/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.60/1.01  --inst_passive_queues_freq              [25;2]
% 1.60/1.01  --inst_dismatching                      true
% 1.60/1.01  --inst_eager_unprocessed_to_passive     true
% 1.60/1.01  --inst_prop_sim_given                   true
% 1.60/1.01  --inst_prop_sim_new                     false
% 1.60/1.01  --inst_subs_new                         false
% 1.60/1.01  --inst_eq_res_simp                      false
% 1.60/1.01  --inst_subs_given                       false
% 1.60/1.01  --inst_orphan_elimination               true
% 1.60/1.01  --inst_learning_loop_flag               true
% 1.60/1.01  --inst_learning_start                   3000
% 1.60/1.01  --inst_learning_factor                  2
% 1.60/1.01  --inst_start_prop_sim_after_learn       3
% 1.60/1.01  --inst_sel_renew                        solver
% 1.60/1.01  --inst_lit_activity_flag                true
% 1.60/1.01  --inst_restr_to_given                   false
% 1.60/1.01  --inst_activity_threshold               500
% 1.60/1.01  --inst_out_proof                        true
% 1.60/1.01  
% 1.60/1.01  ------ Resolution Options
% 1.60/1.01  
% 1.60/1.01  --resolution_flag                       false
% 1.60/1.01  --res_lit_sel                           adaptive
% 1.60/1.01  --res_lit_sel_side                      none
% 1.60/1.01  --res_ordering                          kbo
% 1.60/1.01  --res_to_prop_solver                    active
% 1.60/1.01  --res_prop_simpl_new                    false
% 1.60/1.01  --res_prop_simpl_given                  true
% 1.60/1.01  --res_passive_queue_type                priority_queues
% 1.60/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.60/1.01  --res_passive_queues_freq               [15;5]
% 1.60/1.01  --res_forward_subs                      full
% 1.60/1.01  --res_backward_subs                     full
% 1.60/1.01  --res_forward_subs_resolution           true
% 1.60/1.01  --res_backward_subs_resolution          true
% 1.60/1.01  --res_orphan_elimination                true
% 1.60/1.01  --res_time_limit                        2.
% 1.60/1.01  --res_out_proof                         true
% 1.60/1.01  
% 1.60/1.01  ------ Superposition Options
% 1.60/1.01  
% 1.60/1.01  --superposition_flag                    true
% 1.60/1.01  --sup_passive_queue_type                priority_queues
% 1.60/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.60/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.60/1.01  --demod_completeness_check              fast
% 1.60/1.01  --demod_use_ground                      true
% 1.60/1.01  --sup_to_prop_solver                    passive
% 1.60/1.01  --sup_prop_simpl_new                    true
% 1.60/1.01  --sup_prop_simpl_given                  true
% 1.60/1.01  --sup_fun_splitting                     false
% 1.60/1.01  --sup_smt_interval                      50000
% 1.60/1.01  
% 1.60/1.01  ------ Superposition Simplification Setup
% 1.60/1.01  
% 1.60/1.01  --sup_indices_passive                   []
% 1.60/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.60/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.60/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.60/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.60/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.60/1.01  --sup_full_bw                           [BwDemod]
% 1.60/1.01  --sup_immed_triv                        [TrivRules]
% 1.60/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.60/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.60/1.01  --sup_immed_bw_main                     []
% 1.60/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.60/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.60/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.60/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.60/1.01  
% 1.60/1.01  ------ Combination Options
% 1.60/1.01  
% 1.60/1.01  --comb_res_mult                         3
% 1.60/1.01  --comb_sup_mult                         2
% 1.60/1.01  --comb_inst_mult                        10
% 1.60/1.01  
% 1.60/1.01  ------ Debug Options
% 1.60/1.01  
% 1.60/1.01  --dbg_backtrace                         false
% 1.60/1.01  --dbg_dump_prop_clauses                 false
% 1.60/1.01  --dbg_dump_prop_clauses_file            -
% 1.60/1.01  --dbg_out_stat                          false
% 1.60/1.01  
% 1.60/1.01  
% 1.60/1.01  
% 1.60/1.01  
% 1.60/1.01  ------ Proving...
% 1.60/1.01  
% 1.60/1.01  
% 1.60/1.01  % SZS status Theorem for theBenchmark.p
% 1.60/1.01  
% 1.60/1.01   Resolution empty clause
% 1.60/1.01  
% 1.60/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.60/1.01  
% 1.60/1.01  fof(f9,conjecture,(
% 1.60/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f10,negated_conjecture,(
% 1.60/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 1.60/1.01    inference(negated_conjecture,[],[f9])).
% 1.60/1.01  
% 1.60/1.01  fof(f24,plain,(
% 1.60/1.01    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.60/1.01    inference(ennf_transformation,[],[f10])).
% 1.60/1.01  
% 1.60/1.01  fof(f25,plain,(
% 1.60/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.60/1.01    inference(flattening,[],[f24])).
% 1.60/1.01  
% 1.60/1.01  fof(f29,plain,(
% 1.60/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.60/1.01    introduced(choice_axiom,[])).
% 1.60/1.01  
% 1.60/1.01  fof(f30,plain,(
% 1.60/1.01    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 1.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f29])).
% 1.60/1.01  
% 1.60/1.01  fof(f43,plain,(
% 1.60/1.01    r1_tarski(sK1,sK3)),
% 1.60/1.01    inference(cnf_transformation,[],[f30])).
% 1.60/1.01  
% 1.60/1.01  fof(f6,axiom,(
% 1.60/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f12,plain,(
% 1.60/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.60/1.01    inference(pure_predicate_removal,[],[f6])).
% 1.60/1.01  
% 1.60/1.01  fof(f19,plain,(
% 1.60/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/1.01    inference(ennf_transformation,[],[f12])).
% 1.60/1.01  
% 1.60/1.01  fof(f37,plain,(
% 1.60/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/1.01    inference(cnf_transformation,[],[f19])).
% 1.60/1.01  
% 1.60/1.01  fof(f42,plain,(
% 1.60/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.60/1.01    inference(cnf_transformation,[],[f30])).
% 1.60/1.01  
% 1.60/1.01  fof(f3,axiom,(
% 1.60/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f15,plain,(
% 1.60/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.60/1.01    inference(ennf_transformation,[],[f3])).
% 1.60/1.01  
% 1.60/1.01  fof(f26,plain,(
% 1.60/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.60/1.01    inference(nnf_transformation,[],[f15])).
% 1.60/1.01  
% 1.60/1.01  fof(f33,plain,(
% 1.60/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.60/1.01    inference(cnf_transformation,[],[f26])).
% 1.60/1.01  
% 1.60/1.01  fof(f5,axiom,(
% 1.60/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f18,plain,(
% 1.60/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/1.01    inference(ennf_transformation,[],[f5])).
% 1.60/1.01  
% 1.60/1.01  fof(f36,plain,(
% 1.60/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.60/1.01    inference(cnf_transformation,[],[f18])).
% 1.60/1.01  
% 1.60/1.01  fof(f34,plain,(
% 1.60/1.01    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.60/1.01    inference(cnf_transformation,[],[f26])).
% 1.60/1.01  
% 1.60/1.01  fof(f2,axiom,(
% 1.60/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f14,plain,(
% 1.60/1.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.60/1.01    inference(ennf_transformation,[],[f2])).
% 1.60/1.01  
% 1.60/1.01  fof(f32,plain,(
% 1.60/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.60/1.01    inference(cnf_transformation,[],[f14])).
% 1.60/1.01  
% 1.60/1.01  fof(f1,axiom,(
% 1.60/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f13,plain,(
% 1.60/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.60/1.01    inference(ennf_transformation,[],[f1])).
% 1.60/1.01  
% 1.60/1.01  fof(f31,plain,(
% 1.60/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.60/1.01    inference(cnf_transformation,[],[f13])).
% 1.60/1.01  
% 1.60/1.01  fof(f4,axiom,(
% 1.60/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f16,plain,(
% 1.60/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.60/1.01    inference(ennf_transformation,[],[f4])).
% 1.60/1.01  
% 1.60/1.01  fof(f17,plain,(
% 1.60/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.60/1.01    inference(flattening,[],[f16])).
% 1.60/1.01  
% 1.60/1.01  fof(f35,plain,(
% 1.60/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.60/1.01    inference(cnf_transformation,[],[f17])).
% 1.60/1.01  
% 1.60/1.01  fof(f7,axiom,(
% 1.60/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f20,plain,(
% 1.60/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.60/1.01    inference(ennf_transformation,[],[f7])).
% 1.60/1.01  
% 1.60/1.01  fof(f21,plain,(
% 1.60/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.60/1.01    inference(flattening,[],[f20])).
% 1.60/1.01  
% 1.60/1.01  fof(f38,plain,(
% 1.60/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.60/1.01    inference(cnf_transformation,[],[f21])).
% 1.60/1.01  
% 1.60/1.01  fof(f40,plain,(
% 1.60/1.01    v1_funct_1(sK4)),
% 1.60/1.01    inference(cnf_transformation,[],[f30])).
% 1.60/1.01  
% 1.60/1.01  fof(f41,plain,(
% 1.60/1.01    v1_funct_2(sK4,sK1,sK2)),
% 1.60/1.01    inference(cnf_transformation,[],[f30])).
% 1.60/1.01  
% 1.60/1.01  fof(f8,axiom,(
% 1.60/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.60/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.60/1.01  
% 1.60/1.01  fof(f11,plain,(
% 1.60/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : k1_funct_1(X2,X4) = k1_funct_1(X3,X4) => r2_relset_1(X0,X1,X2,X3))))),
% 1.60/1.01    inference(pure_predicate_removal,[],[f8])).
% 1.60/1.01  
% 1.60/1.01  fof(f22,plain,(
% 1.60/1.01    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.60/1.01    inference(ennf_transformation,[],[f11])).
% 1.60/1.01  
% 1.60/1.01  fof(f23,plain,(
% 1.60/1.01    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/1.01    inference(flattening,[],[f22])).
% 1.60/1.01  
% 1.60/1.01  fof(f27,plain,(
% 1.60/1.01    ! [X3,X2] : (? [X4] : k1_funct_1(X2,X4) != k1_funct_1(X3,X4) => k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)))),
% 1.60/1.01    introduced(choice_axiom,[])).
% 1.60/1.01  
% 1.60/1.01  fof(f28,plain,(
% 1.60/1.01    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f27])).
% 1.60/1.01  
% 1.60/1.01  fof(f39,plain,(
% 1.60/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X2,X3)) != k1_funct_1(X3,sK0(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.60/1.01    inference(cnf_transformation,[],[f28])).
% 1.60/1.01  
% 1.60/1.01  fof(f44,plain,(
% 1.60/1.01    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)),
% 1.60/1.01    inference(cnf_transformation,[],[f30])).
% 1.60/1.01  
% 1.60/1.01  cnf(c_10,negated_conjecture,
% 1.60/1.01      ( r1_tarski(sK1,sK3) ),
% 1.60/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_800,plain,
% 1.60/1.01      ( r1_tarski(sK1,sK3) = iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_6,plain,
% 1.60/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 1.60/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_11,negated_conjecture,
% 1.60/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.60/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_271,plain,
% 1.60/1.01      ( v4_relat_1(X0,X1)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | sK4 != X0 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_272,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.60/1.01      inference(unflattening,[status(thm)],[c_271]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_799,plain,
% 1.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | v4_relat_1(sK4,X0) = iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_888,plain,
% 1.60/1.01      ( v4_relat_1(sK4,sK1) = iProver_top ),
% 1.60/1.01      inference(equality_resolution,[status(thm)],[c_799]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_3,plain,
% 1.60/1.01      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 1.60/1.01      inference(cnf_transformation,[],[f33]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_5,plain,
% 1.60/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.60/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_283,plain,
% 1.60/1.01      ( v1_relat_1(X0)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | sK4 != X0 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_284,plain,
% 1.60/1.01      ( v1_relat_1(sK4)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.60/1.01      inference(unflattening,[status(thm)],[c_283]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_351,plain,
% 1.60/1.01      ( ~ v4_relat_1(X0,X1)
% 1.60/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | sK4 != X0 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_284]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_352,plain,
% 1.60/1.01      ( ~ v4_relat_1(sK4,X0)
% 1.60/1.01      | r1_tarski(k1_relat_1(sK4),X0)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.60/1.01      inference(unflattening,[status(thm)],[c_351]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_555,plain,
% 1.60/1.01      ( ~ v4_relat_1(sK4,X0)
% 1.60/1.01      | r1_tarski(k1_relat_1(sK4),X0)
% 1.60/1.01      | ~ sP2_iProver_split ),
% 1.60/1.01      inference(splitting,
% 1.60/1.01                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 1.60/1.01                [c_352]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_794,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0) != iProver_top
% 1.60/1.01      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 1.60/1.01      | sP2_iProver_split != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_556,plain,
% 1.60/1.01      ( sP2_iProver_split | sP0_iProver_split ),
% 1.60/1.01      inference(splitting,
% 1.60/1.01                [splitting(split),new_symbols(definition,[])],
% 1.60/1.01                [c_352]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_589,plain,
% 1.60/1.01      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_590,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0) != iProver_top
% 1.60/1.01      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 1.60/1.01      | sP2_iProver_split != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_560,plain,( X0 = X0 ),theory(equality) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_900,plain,
% 1.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.60/1.01      inference(instantiation,[status(thm)],[c_560]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_2,plain,
% 1.60/1.01      ( v4_relat_1(X0,X1) | ~ r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 1.60/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_366,plain,
% 1.60/1.01      ( v4_relat_1(X0,X1)
% 1.60/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | sK4 != X0 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_284]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_367,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0)
% 1.60/1.01      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.60/1.01      inference(unflattening,[status(thm)],[c_366]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_552,plain,
% 1.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | ~ sP0_iProver_split ),
% 1.60/1.01      inference(splitting,
% 1.60/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.60/1.01                [c_367]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_902,plain,
% 1.60/1.01      ( ~ sP0_iProver_split
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.60/1.01      inference(instantiation,[status(thm)],[c_552]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_906,plain,
% 1.60/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | sP0_iProver_split != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1215,plain,
% 1.60/1.01      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 1.60/1.01      | v4_relat_1(sK4,X0) != iProver_top ),
% 1.60/1.01      inference(global_propositional_subsumption,
% 1.60/1.01                [status(thm)],
% 1.60/1.01                [c_794,c_589,c_590,c_900,c_906]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1216,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0) != iProver_top
% 1.60/1.01      | r1_tarski(k1_relat_1(sK4),X0) = iProver_top ),
% 1.60/1.01      inference(renaming,[status(thm)],[c_1215]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1,plain,
% 1.60/1.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.60/1.01      inference(cnf_transformation,[],[f32]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_801,plain,
% 1.60/1.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1223,plain,
% 1.60/1.01      ( k2_xboole_0(k1_relat_1(sK4),X0) = X0
% 1.60/1.01      | v4_relat_1(sK4,X0) != iProver_top ),
% 1.60/1.01      inference(superposition,[status(thm)],[c_1216,c_801]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1435,plain,
% 1.60/1.01      ( k2_xboole_0(k1_relat_1(sK4),sK1) = sK1 ),
% 1.60/1.01      inference(superposition,[status(thm)],[c_888,c_1223]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_0,plain,
% 1.60/1.01      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 1.60/1.01      inference(cnf_transformation,[],[f31]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_802,plain,
% 1.60/1.01      ( r1_tarski(X0,X1) = iProver_top
% 1.60/1.01      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1535,plain,
% 1.60/1.01      ( r1_tarski(k1_relat_1(sK4),X0) = iProver_top
% 1.60/1.01      | r1_tarski(sK1,X0) != iProver_top ),
% 1.60/1.01      inference(superposition,[status(thm)],[c_1435,c_802]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_553,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0)
% 1.60/1.01      | ~ r1_tarski(k1_relat_1(sK4),X0)
% 1.60/1.01      | ~ sP1_iProver_split ),
% 1.60/1.01      inference(splitting,
% 1.60/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.60/1.01                [c_367]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_791,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0) = iProver_top
% 1.60/1.01      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 1.60/1.01      | sP1_iProver_split != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_554,plain,
% 1.60/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 1.60/1.01      inference(splitting,
% 1.60/1.01                [splitting(split),new_symbols(definition,[])],
% 1.60/1.01                [c_367]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_582,plain,
% 1.60/1.01      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_583,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0) = iProver_top
% 1.60/1.01      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 1.60/1.01      | sP1_iProver_split != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1057,plain,
% 1.60/1.01      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 1.60/1.01      | v4_relat_1(sK4,X0) = iProver_top ),
% 1.60/1.01      inference(global_propositional_subsumption,
% 1.60/1.01                [status(thm)],
% 1.60/1.01                [c_791,c_582,c_583,c_900,c_906]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1058,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0) = iProver_top
% 1.60/1.01      | r1_tarski(k1_relat_1(sK4),X0) != iProver_top ),
% 1.60/1.01      inference(renaming,[status(thm)],[c_1057]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1543,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0) = iProver_top | r1_tarski(sK1,X0) != iProver_top ),
% 1.60/1.01      inference(superposition,[status(thm)],[c_1535,c_1058]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1731,plain,
% 1.60/1.01      ( v4_relat_1(sK4,sK3) = iProver_top ),
% 1.60/1.01      inference(superposition,[status(thm)],[c_800,c_1543]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_4,plain,
% 1.60/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.60/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_336,plain,
% 1.60/1.01      ( ~ v4_relat_1(X0,X1)
% 1.60/1.01      | k7_relat_1(X0,X1) = X0
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | sK4 != X0 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_284]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_337,plain,
% 1.60/1.01      ( ~ v4_relat_1(sK4,X0)
% 1.60/1.01      | k7_relat_1(sK4,X0) = sK4
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.60/1.01      inference(unflattening,[status(thm)],[c_336]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_557,plain,
% 1.60/1.01      ( ~ v4_relat_1(sK4,X0) | k7_relat_1(sK4,X0) = sK4 | ~ sP3_iProver_split ),
% 1.60/1.01      inference(splitting,
% 1.60/1.01                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 1.60/1.01                [c_337]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_797,plain,
% 1.60/1.01      ( k7_relat_1(sK4,X0) = sK4
% 1.60/1.01      | v4_relat_1(sK4,X0) != iProver_top
% 1.60/1.01      | sP3_iProver_split != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_558,plain,
% 1.60/1.01      ( sP3_iProver_split | sP0_iProver_split ),
% 1.60/1.01      inference(splitting,
% 1.60/1.01                [splitting(split),new_symbols(definition,[])],
% 1.60/1.01                [c_337]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_594,plain,
% 1.60/1.01      ( sP3_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_595,plain,
% 1.60/1.01      ( k7_relat_1(sK4,X0) = sK4
% 1.60/1.01      | v4_relat_1(sK4,X0) != iProver_top
% 1.60/1.01      | sP3_iProver_split != iProver_top ),
% 1.60/1.01      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_976,plain,
% 1.60/1.01      ( v4_relat_1(sK4,X0) != iProver_top | k7_relat_1(sK4,X0) = sK4 ),
% 1.60/1.01      inference(global_propositional_subsumption,
% 1.60/1.01                [status(thm)],
% 1.60/1.01                [c_797,c_594,c_595,c_900,c_906]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_977,plain,
% 1.60/1.01      ( k7_relat_1(sK4,X0) = sK4 | v4_relat_1(sK4,X0) != iProver_top ),
% 1.60/1.01      inference(renaming,[status(thm)],[c_976]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1736,plain,
% 1.60/1.01      ( k7_relat_1(sK4,sK3) = sK4 ),
% 1.60/1.01      inference(superposition,[status(thm)],[c_1731,c_977]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_7,plain,
% 1.60/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.60/1.01      | ~ v1_funct_1(X0)
% 1.60/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.60/1.01      inference(cnf_transformation,[],[f38]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_13,negated_conjecture,
% 1.60/1.01      ( v1_funct_1(sK4) ),
% 1.60/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_212,plain,
% 1.60/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.60/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 1.60/1.01      | sK4 != X0 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_213,plain,
% 1.60/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.60/1.01      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 1.60/1.01      inference(unflattening,[status(thm)],[c_212]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_311,plain,
% 1.60/1.01      ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | sK4 != sK4 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_213]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_454,plain,
% 1.60/1.01      ( k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_311]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_915,plain,
% 1.60/1.01      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 1.60/1.01      inference(equality_resolution,[status(thm)],[c_454]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_12,negated_conjecture,
% 1.60/1.01      ( v1_funct_2(sK4,sK1,sK2) ),
% 1.60/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_8,plain,
% 1.60/1.01      ( r2_relset_1(X0,X1,X2,X3)
% 1.60/1.01      | ~ v1_funct_2(X3,X0,X1)
% 1.60/1.01      | ~ v1_funct_2(X2,X0,X1)
% 1.60/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.60/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.60/1.01      | ~ v1_funct_1(X2)
% 1.60/1.01      | ~ v1_funct_1(X3)
% 1.60/1.01      | k1_funct_1(X3,sK0(X2,X3)) != k1_funct_1(X2,sK0(X2,X3)) ),
% 1.60/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_9,negated_conjecture,
% 1.60/1.01      ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
% 1.60/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_160,plain,
% 1.60/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.60/1.01      | ~ v1_funct_2(X3,X1,X2)
% 1.60/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.60/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.60/1.01      | ~ v1_funct_1(X0)
% 1.60/1.01      | ~ v1_funct_1(X3)
% 1.60/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != X3
% 1.60/1.01      | k1_funct_1(X3,sK0(X3,X0)) != k1_funct_1(X0,sK0(X3,X0))
% 1.60/1.01      | sK4 != X0
% 1.60/1.01      | sK2 != X2
% 1.60/1.01      | sK1 != X1 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_161,plain,
% 1.60/1.01      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 1.60/1.01      | ~ v1_funct_2(sK4,sK1,sK2)
% 1.60/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.60/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.60/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 1.60/1.01      | ~ v1_funct_1(sK4)
% 1.60/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 1.60/1.01      inference(unflattening,[status(thm)],[c_160]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_163,plain,
% 1.60/1.01      ( ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 1.60/1.01      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 1.60/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.60/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 1.60/1.01      inference(global_propositional_subsumption,
% 1.60/1.01                [status(thm)],
% 1.60/1.01                [c_161,c_13,c_12,c_11]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_164,plain,
% 1.60/1.01      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 1.60/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.60/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 1.60/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 1.60/1.01      inference(renaming,[status(thm)],[c_163]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_224,plain,
% 1.60/1.01      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK1,sK2)
% 1.60/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.60/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 1.60/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_164]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_247,plain,
% 1.60/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.60/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 1.60/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 1.60/1.01      | sK2 != sK2
% 1.60/1.01      | sK1 != sK1 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_224]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_295,plain,
% 1.60/1.01      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 1.60/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4))
% 1.60/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.60/1.01      | sK2 != sK2
% 1.60/1.01      | sK1 != sK1 ),
% 1.60/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_247]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_456,plain,
% 1.60/1.01      ( k2_partfun1(sK1,sK2,sK4,sK3) != sK4
% 1.60/1.01      | k1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3),sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k2_partfun1(sK1,sK2,sK4,sK3),sK4)) ),
% 1.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_295]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_946,plain,
% 1.60/1.01      ( k1_funct_1(k7_relat_1(sK4,sK3),sK0(k7_relat_1(sK4,sK3),sK4)) != k1_funct_1(sK4,sK0(k7_relat_1(sK4,sK3),sK4))
% 1.60/1.01      | k7_relat_1(sK4,sK3) != sK4 ),
% 1.60/1.01      inference(demodulation,[status(thm)],[c_915,c_456]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1778,plain,
% 1.60/1.01      ( k1_funct_1(sK4,sK0(sK4,sK4)) != k1_funct_1(sK4,sK0(sK4,sK4))
% 1.60/1.01      | sK4 != sK4 ),
% 1.60/1.01      inference(demodulation,[status(thm)],[c_1736,c_946]) ).
% 1.60/1.01  
% 1.60/1.01  cnf(c_1858,plain,
% 1.60/1.01      ( $false ),
% 1.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_1778]) ).
% 1.60/1.01  
% 1.60/1.01  
% 1.60/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.60/1.01  
% 1.60/1.01  ------                               Statistics
% 1.60/1.01  
% 1.60/1.01  ------ General
% 1.60/1.01  
% 1.60/1.01  abstr_ref_over_cycles:                  0
% 1.60/1.01  abstr_ref_under_cycles:                 0
% 1.60/1.01  gc_basic_clause_elim:                   0
% 1.60/1.01  forced_gc_time:                         0
% 1.60/1.01  parsing_time:                           0.016
% 1.60/1.01  unif_index_cands_time:                  0.
% 1.60/1.01  unif_index_add_time:                    0.
% 1.60/1.01  orderings_time:                         0.
% 1.60/1.01  out_proof_time:                         0.014
% 1.60/1.01  total_time:                             0.106
% 1.60/1.01  num_of_symbols:                         54
% 1.60/1.01  num_of_terms:                           1572
% 1.60/1.01  
% 1.60/1.01  ------ Preprocessing
% 1.60/1.01  
% 1.60/1.01  num_of_splits:                          6
% 1.60/1.01  num_of_split_atoms:                     4
% 1.60/1.01  num_of_reused_defs:                     2
% 1.60/1.01  num_eq_ax_congr_red:                    19
% 1.60/1.01  num_of_sem_filtered_clauses:            1
% 1.60/1.01  num_of_subtypes:                        0
% 1.60/1.01  monotx_restored_types:                  0
% 1.60/1.01  sat_num_of_epr_types:                   0
% 1.60/1.01  sat_num_of_non_cyclic_types:            0
% 1.60/1.01  sat_guarded_non_collapsed_types:        0
% 1.60/1.01  num_pure_diseq_elim:                    0
% 1.60/1.01  simp_replaced_by:                       0
% 1.60/1.01  res_preprocessed:                       72
% 1.60/1.01  prep_upred:                             0
% 1.60/1.01  prep_unflattend:                        10
% 1.60/1.01  smt_new_axioms:                         0
% 1.60/1.01  pred_elim_cands:                        2
% 1.60/1.01  pred_elim:                              5
% 1.60/1.01  pred_elim_cl:                           5
% 1.60/1.01  pred_elim_cycles:                       8
% 1.60/1.01  merged_defs:                            0
% 1.60/1.01  merged_defs_ncl:                        0
% 1.60/1.01  bin_hyper_res:                          0
% 1.60/1.01  prep_cycles:                            4
% 1.60/1.01  pred_elim_time:                         0.007
% 1.60/1.01  splitting_time:                         0.
% 1.60/1.01  sem_filter_time:                        0.
% 1.60/1.01  monotx_time:                            0.
% 1.60/1.01  subtype_inf_time:                       0.
% 1.60/1.01  
% 1.60/1.01  ------ Problem properties
% 1.60/1.01  
% 1.60/1.01  clauses:                                15
% 1.60/1.01  conjectures:                            1
% 1.60/1.01  epr:                                    4
% 1.60/1.01  horn:                                   12
% 1.60/1.01  ground:                                 5
% 1.60/1.01  unary:                                  1
% 1.60/1.01  binary:                                 11
% 1.60/1.01  lits:                                   32
% 1.60/1.01  lits_eq:                                10
% 1.60/1.01  fd_pure:                                0
% 1.60/1.01  fd_pseudo:                              0
% 1.60/1.01  fd_cond:                                0
% 1.60/1.01  fd_pseudo_cond:                         0
% 1.60/1.01  ac_symbols:                             0
% 1.60/1.01  
% 1.60/1.01  ------ Propositional Solver
% 1.60/1.01  
% 1.60/1.01  prop_solver_calls:                      27
% 1.60/1.01  prop_fast_solver_calls:                 487
% 1.60/1.01  smt_solver_calls:                       0
% 1.60/1.01  smt_fast_solver_calls:                  0
% 1.60/1.01  prop_num_of_clauses:                    610
% 1.60/1.01  prop_preprocess_simplified:             2518
% 1.60/1.01  prop_fo_subsumed:                       12
% 1.60/1.01  prop_solver_time:                       0.
% 1.60/1.01  smt_solver_time:                        0.
% 1.60/1.01  smt_fast_solver_time:                   0.
% 1.60/1.01  prop_fast_solver_time:                  0.
% 1.60/1.01  prop_unsat_core_time:                   0.
% 1.60/1.01  
% 1.60/1.01  ------ QBF
% 1.60/1.01  
% 1.60/1.01  qbf_q_res:                              0
% 1.60/1.01  qbf_num_tautologies:                    0
% 1.60/1.01  qbf_prep_cycles:                        0
% 1.60/1.01  
% 1.60/1.01  ------ BMC1
% 1.60/1.01  
% 1.60/1.01  bmc1_current_bound:                     -1
% 1.60/1.01  bmc1_last_solved_bound:                 -1
% 1.60/1.01  bmc1_unsat_core_size:                   -1
% 1.60/1.01  bmc1_unsat_core_parents_size:           -1
% 1.60/1.01  bmc1_merge_next_fun:                    0
% 1.60/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.60/1.01  
% 1.60/1.01  ------ Instantiation
% 1.60/1.01  
% 1.60/1.01  inst_num_of_clauses:                    209
% 1.60/1.01  inst_num_in_passive:                    22
% 1.60/1.01  inst_num_in_active:                     146
% 1.60/1.01  inst_num_in_unprocessed:                41
% 1.60/1.01  inst_num_of_loops:                      160
% 1.60/1.01  inst_num_of_learning_restarts:          0
% 1.60/1.01  inst_num_moves_active_passive:          10
% 1.60/1.01  inst_lit_activity:                      0
% 1.60/1.01  inst_lit_activity_moves:                0
% 1.60/1.01  inst_num_tautologies:                   0
% 1.60/1.01  inst_num_prop_implied:                  0
% 1.60/1.01  inst_num_existing_simplified:           0
% 1.60/1.01  inst_num_eq_res_simplified:             0
% 1.60/1.01  inst_num_child_elim:                    0
% 1.60/1.01  inst_num_of_dismatching_blockings:      53
% 1.60/1.01  inst_num_of_non_proper_insts:           208
% 1.60/1.01  inst_num_of_duplicates:                 0
% 1.60/1.01  inst_inst_num_from_inst_to_res:         0
% 1.60/1.01  inst_dismatching_checking_time:         0.
% 1.60/1.01  
% 1.60/1.01  ------ Resolution
% 1.60/1.01  
% 1.60/1.01  res_num_of_clauses:                     0
% 1.60/1.01  res_num_in_passive:                     0
% 1.60/1.01  res_num_in_active:                      0
% 1.60/1.01  res_num_of_loops:                       76
% 1.60/1.01  res_forward_subset_subsumed:            24
% 1.60/1.01  res_backward_subset_subsumed:           0
% 1.60/1.01  res_forward_subsumed:                   0
% 1.60/1.01  res_backward_subsumed:                  0
% 1.60/1.01  res_forward_subsumption_resolution:     0
% 1.60/1.01  res_backward_subsumption_resolution:    0
% 1.60/1.01  res_clause_to_clause_subsumption:       30
% 1.60/1.01  res_orphan_elimination:                 0
% 1.60/1.01  res_tautology_del:                      35
% 1.60/1.01  res_num_eq_res_simplified:              2
% 1.60/1.01  res_num_sel_changes:                    0
% 1.60/1.01  res_moves_from_active_to_pass:          0
% 1.60/1.01  
% 1.60/1.01  ------ Superposition
% 1.60/1.01  
% 1.60/1.01  sup_time_total:                         0.
% 1.60/1.01  sup_time_generating:                    0.
% 1.60/1.01  sup_time_sim_full:                      0.
% 1.60/1.01  sup_time_sim_immed:                     0.
% 1.60/1.01  
% 1.60/1.01  sup_num_of_clauses:                     29
% 1.60/1.01  sup_num_in_active:                      28
% 1.60/1.01  sup_num_in_passive:                     1
% 1.60/1.01  sup_num_of_loops:                       30
% 1.60/1.01  sup_fw_superposition:                   5
% 1.60/1.01  sup_bw_superposition:                   11
% 1.60/1.01  sup_immediate_simplified:               0
% 1.60/1.01  sup_given_eliminated:                   0
% 1.60/1.01  comparisons_done:                       0
% 1.60/1.01  comparisons_avoided:                    0
% 1.60/1.01  
% 1.60/1.01  ------ Simplifications
% 1.60/1.01  
% 1.60/1.01  
% 1.60/1.01  sim_fw_subset_subsumed:                 0
% 1.60/1.01  sim_bw_subset_subsumed:                 0
% 1.60/1.01  sim_fw_subsumed:                        0
% 1.60/1.01  sim_bw_subsumed:                        0
% 1.60/1.01  sim_fw_subsumption_res:                 0
% 1.60/1.01  sim_bw_subsumption_res:                 0
% 1.60/1.01  sim_tautology_del:                      1
% 1.60/1.01  sim_eq_tautology_del:                   0
% 1.60/1.01  sim_eq_res_simp:                        0
% 1.60/1.01  sim_fw_demodulated:                     0
% 1.60/1.01  sim_bw_demodulated:                     2
% 1.60/1.01  sim_light_normalised:                   0
% 1.60/1.01  sim_joinable_taut:                      0
% 1.60/1.01  sim_joinable_simp:                      0
% 1.60/1.01  sim_ac_normalised:                      0
% 1.60/1.01  sim_smt_subsumption:                    0
% 1.60/1.01  
%------------------------------------------------------------------------------
