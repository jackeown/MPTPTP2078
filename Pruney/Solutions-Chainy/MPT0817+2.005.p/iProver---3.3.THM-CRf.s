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
% DateTime   : Thu Dec  3 11:54:46 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 146 expanded)
%              Number of clauses        :   50 (  64 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  222 ( 385 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( r1_tarski(k1_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(k1_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(k1_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(k1_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).

fof(f42,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1204,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X0))
    | r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(resolution,[status(thm)],[c_4,c_3])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4941,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1204,c_11])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_137,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_137,c_14])).

cnf(c_223,plain,
    ( ~ r1_tarski(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_360,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1412,plain,
    ( ~ r1_tarski(sK3,X0)
    | k2_zfmisc_1(sK1,sK2) != X0 ),
    inference(resolution,[status(thm)],[c_223,c_360])).

cnf(c_2202,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),X0)
    | ~ r1_tarski(sK3,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1412])).

cnf(c_356,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_728,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_729,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_772,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2466,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
    | ~ r1_tarski(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_728,c_729,c_772])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2579,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK2)) ),
    inference(resolution,[status(thm)],[c_2466,c_5])).

cnf(c_15369,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_4941,c_2579])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1449,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11456,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_1445,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK2)
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2948,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k2_zfmisc_1(X1,sK2)))
    | r1_tarski(X0,sK2)
    | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X1,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_7522,plain,
    ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK2)),sK2)
    | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k2_zfmisc_1(sK0,sK2)))
    | r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2948])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_97,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_8,c_6])).

cnf(c_98,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_97])).

cnf(c_712,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(k2_relat_1(X0),k2_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_1723,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_relat_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1162,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_162,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_137])).

cnf(c_681,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_1085,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_134,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_234,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_135,c_16])).

cnf(c_235,plain,
    ( r1_tarski(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_733,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_732,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15369,c_11456,c_7522,c_1723,c_1162,c_1085,c_733,c_732,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n010.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 19:16:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.87/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/0.96  
% 3.87/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.96  
% 3.87/0.96  ------  iProver source info
% 3.87/0.96  
% 3.87/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.96  git: non_committed_changes: false
% 3.87/0.96  git: last_make_outside_of_git: false
% 3.87/0.96  
% 3.87/0.96  ------ 
% 3.87/0.96  ------ Parsing...
% 3.87/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.96  
% 3.87/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.87/0.96  
% 3.87/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.96  
% 3.87/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.96  ------ Proving...
% 3.87/0.96  ------ Problem Properties 
% 3.87/0.96  
% 3.87/0.96  
% 3.87/0.96  clauses                                 15
% 3.87/0.96  conjectures                             1
% 3.87/0.96  EPR                                     4
% 3.87/0.96  Horn                                    15
% 3.87/0.96  unary                                   5
% 3.87/0.96  binary                                  5
% 3.87/0.96  lits                                    30
% 3.87/0.96  lits eq                                 4
% 3.87/0.96  fd_pure                                 0
% 3.87/0.96  fd_pseudo                               0
% 3.87/0.96  fd_cond                                 0
% 3.87/0.96  fd_pseudo_cond                          1
% 3.87/0.96  AC symbols                              0
% 3.87/0.96  
% 3.87/0.96  ------ Input Options Time Limit: Unbounded
% 3.87/0.96  
% 3.87/0.96  
% 3.87/0.96  ------ 
% 3.87/0.96  Current options:
% 3.87/0.96  ------ 
% 3.87/0.96  
% 3.87/0.96  
% 3.87/0.96  
% 3.87/0.96  
% 3.87/0.96  ------ Proving...
% 3.87/0.96  
% 3.87/0.96  
% 3.87/0.96  % SZS status Theorem for theBenchmark.p
% 3.87/0.96  
% 3.87/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.96  
% 3.87/0.96  fof(f3,axiom,(
% 3.87/0.96    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.87/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.96  
% 3.87/0.96  fof(f14,plain,(
% 3.87/0.96    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.87/0.96    inference(ennf_transformation,[],[f3])).
% 3.87/0.96  
% 3.87/0.96  fof(f31,plain,(
% 3.87/0.96    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.87/0.96    inference(cnf_transformation,[],[f14])).
% 3.87/0.96  
% 3.87/0.96  fof(f2,axiom,(
% 3.87/0.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f12,plain,(
% 3.87/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.87/0.97    inference(ennf_transformation,[],[f2])).
% 3.87/0.97  
% 3.87/0.97  fof(f13,plain,(
% 3.87/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.87/0.97    inference(flattening,[],[f12])).
% 3.87/0.97  
% 3.87/0.97  fof(f29,plain,(
% 3.87/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.87/0.97    inference(cnf_transformation,[],[f13])).
% 3.87/0.97  
% 3.87/0.97  fof(f8,axiom,(
% 3.87/0.97    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f16,plain,(
% 3.87/0.97    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.87/0.97    inference(ennf_transformation,[],[f8])).
% 3.87/0.97  
% 3.87/0.97  fof(f37,plain,(
% 3.87/0.97    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 3.87/0.97    inference(cnf_transformation,[],[f16])).
% 3.87/0.97  
% 3.87/0.97  fof(f1,axiom,(
% 3.87/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f21,plain,(
% 3.87/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.87/0.97    inference(nnf_transformation,[],[f1])).
% 3.87/0.97  
% 3.87/0.97  fof(f22,plain,(
% 3.87/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.87/0.97    inference(flattening,[],[f21])).
% 3.87/0.97  
% 3.87/0.97  fof(f28,plain,(
% 3.87/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.87/0.97    inference(cnf_transformation,[],[f22])).
% 3.87/0.97  
% 3.87/0.97  fof(f4,axiom,(
% 3.87/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f23,plain,(
% 3.87/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.87/0.97    inference(nnf_transformation,[],[f4])).
% 3.87/0.97  
% 3.87/0.97  fof(f33,plain,(
% 3.87/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.87/0.97    inference(cnf_transformation,[],[f23])).
% 3.87/0.97  
% 3.87/0.97  fof(f10,conjecture,(
% 3.87/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f11,negated_conjecture,(
% 3.87/0.97    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.87/0.97    inference(negated_conjecture,[],[f10])).
% 3.87/0.97  
% 3.87/0.97  fof(f19,plain,(
% 3.87/0.97    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.87/0.97    inference(ennf_transformation,[],[f11])).
% 3.87/0.97  
% 3.87/0.97  fof(f20,plain,(
% 3.87/0.97    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.87/0.97    inference(flattening,[],[f19])).
% 3.87/0.97  
% 3.87/0.97  fof(f24,plain,(
% 3.87/0.97    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 3.87/0.97    introduced(choice_axiom,[])).
% 3.87/0.97  
% 3.87/0.97  fof(f25,plain,(
% 3.87/0.97    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 3.87/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24])).
% 3.87/0.97  
% 3.87/0.97  fof(f42,plain,(
% 3.87/0.97    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.87/0.97    inference(cnf_transformation,[],[f25])).
% 3.87/0.97  
% 3.87/0.97  fof(f30,plain,(
% 3.87/0.97    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.87/0.97    inference(cnf_transformation,[],[f14])).
% 3.87/0.97  
% 3.87/0.97  fof(f7,axiom,(
% 3.87/0.97    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f36,plain,(
% 3.87/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 3.87/0.97    inference(cnf_transformation,[],[f7])).
% 3.87/0.97  
% 3.87/0.97  fof(f9,axiom,(
% 3.87/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f17,plain,(
% 3.87/0.97    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.87/0.97    inference(ennf_transformation,[],[f9])).
% 3.87/0.97  
% 3.87/0.97  fof(f18,plain,(
% 3.87/0.97    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.87/0.97    inference(flattening,[],[f17])).
% 3.87/0.97  
% 3.87/0.97  fof(f39,plain,(
% 3.87/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.87/0.97    inference(cnf_transformation,[],[f18])).
% 3.87/0.97  
% 3.87/0.97  fof(f5,axiom,(
% 3.87/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f15,plain,(
% 3.87/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.87/0.97    inference(ennf_transformation,[],[f5])).
% 3.87/0.97  
% 3.87/0.97  fof(f34,plain,(
% 3.87/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.87/0.97    inference(cnf_transformation,[],[f15])).
% 3.87/0.97  
% 3.87/0.97  fof(f6,axiom,(
% 3.87/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.87/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.97  
% 3.87/0.97  fof(f35,plain,(
% 3.87/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.87/0.97    inference(cnf_transformation,[],[f6])).
% 3.87/0.97  
% 3.87/0.97  fof(f32,plain,(
% 3.87/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.87/0.97    inference(cnf_transformation,[],[f23])).
% 3.87/0.97  
% 3.87/0.97  fof(f40,plain,(
% 3.87/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 3.87/0.97    inference(cnf_transformation,[],[f25])).
% 3.87/0.97  
% 3.87/0.97  fof(f41,plain,(
% 3.87/0.97    r1_tarski(k1_relat_1(sK3),sK1)),
% 3.87/0.97    inference(cnf_transformation,[],[f25])).
% 3.87/0.97  
% 3.87/0.97  cnf(c_4,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1)
% 3.87/0.97      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 3.87/0.97      inference(cnf_transformation,[],[f31]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_3,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.87/0.97      inference(cnf_transformation,[],[f29]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_1204,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1)
% 3.87/0.97      | ~ r1_tarski(X2,k2_zfmisc_1(X3,X0))
% 3.87/0.97      | r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
% 3.87/0.97      inference(resolution,[status(thm)],[c_4,c_3]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_11,plain,
% 3.87/0.97      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 3.87/0.97      | ~ v1_relat_1(X0) ),
% 3.87/0.97      inference(cnf_transformation,[],[f37]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_4941,plain,
% 3.87/0.97      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),X1))
% 3.87/0.97      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.87/0.97      | ~ v1_relat_1(X0) ),
% 3.87/0.97      inference(resolution,[status(thm)],[c_1204,c_11]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_0,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.87/0.97      inference(cnf_transformation,[],[f28]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_6,plain,
% 3.87/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.87/0.97      inference(cnf_transformation,[],[f33]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_136,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.87/0.97      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_137,plain,
% 3.87/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.87/0.97      inference(renaming,[status(thm)],[c_136]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_14,negated_conjecture,
% 3.87/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.87/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_222,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1)
% 3.87/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X1)
% 3.87/0.97      | sK3 != X0 ),
% 3.87/0.97      inference(resolution_lifted,[status(thm)],[c_137,c_14]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_223,plain,
% 3.87/0.97      ( ~ r1_tarski(sK3,X0)
% 3.87/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(X0) ),
% 3.87/0.97      inference(unflattening,[status(thm)],[c_222]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_360,plain,
% 3.87/0.97      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.87/0.97      theory(equality) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_1412,plain,
% 3.87/0.97      ( ~ r1_tarski(sK3,X0) | k2_zfmisc_1(sK1,sK2) != X0 ),
% 3.87/0.97      inference(resolution,[status(thm)],[c_223,c_360]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_2202,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
% 3.87/0.97      | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),X0)
% 3.87/0.97      | ~ r1_tarski(sK3,X0) ),
% 3.87/0.97      inference(resolution,[status(thm)],[c_0,c_1412]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_356,plain,( X0 = X0 ),theory(equality) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_728,plain,
% 3.87/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_356]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_729,plain,
% 3.87/0.97      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
% 3.87/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_223]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_772,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2))
% 3.87/0.97      | ~ r1_tarski(sK3,X0)
% 3.87/0.97      | r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_2466,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,k2_zfmisc_1(sK1,sK2)) | ~ r1_tarski(sK3,X0) ),
% 3.87/0.97      inference(global_propositional_subsumption,
% 3.87/0.97                [status(thm)],
% 3.87/0.97                [c_2202,c_728,c_729,c_772]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_5,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1)
% 3.87/0.97      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 3.87/0.97      inference(cnf_transformation,[],[f30]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_2579,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK3,k2_zfmisc_1(X0,sK2)) ),
% 3.87/0.97      inference(resolution,[status(thm)],[c_2466,c_5]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_15369,plain,
% 3.87/0.97      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
% 3.87/0.97      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.87/0.97      | ~ v1_relat_1(sK3) ),
% 3.87/0.97      inference(resolution,[status(thm)],[c_4941,c_2579]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_10,plain,
% 3.87/0.97      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
% 3.87/0.97      inference(cnf_transformation,[],[f36]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_1449,plain,
% 3.87/0.97      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,sK2)),sK2) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_11456,plain,
% 3.87/0.97      ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK2)),sK2) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_1449]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_1445,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK2) | r1_tarski(X0,sK2) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_2948,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,k2_relat_1(k2_zfmisc_1(X1,sK2)))
% 3.87/0.97      | r1_tarski(X0,sK2)
% 3.87/0.97      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X1,sK2)),sK2) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_1445]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_7522,plain,
% 3.87/0.97      ( ~ r1_tarski(k2_relat_1(k2_zfmisc_1(sK0,sK2)),sK2)
% 3.87/0.97      | ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k2_zfmisc_1(sK0,sK2)))
% 3.87/0.97      | r1_tarski(k2_relat_1(sK3),sK2) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_2948]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_12,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1)
% 3.87/0.97      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.87/0.97      | ~ v1_relat_1(X0)
% 3.87/0.97      | ~ v1_relat_1(X1) ),
% 3.87/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_8,plain,
% 3.87/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.87/0.97      | ~ v1_relat_1(X1)
% 3.87/0.97      | v1_relat_1(X0) ),
% 3.87/0.97      inference(cnf_transformation,[],[f34]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_97,plain,
% 3.87/0.97      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.87/0.97      | ~ r1_tarski(X0,X1)
% 3.87/0.97      | ~ v1_relat_1(X1) ),
% 3.87/0.97      inference(global_propositional_subsumption,
% 3.87/0.97                [status(thm)],
% 3.87/0.97                [c_12,c_8,c_6]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_98,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1)
% 3.87/0.97      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.87/0.97      | ~ v1_relat_1(X1) ),
% 3.87/0.97      inference(renaming,[status(thm)],[c_97]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_712,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.87/0.97      | r1_tarski(k2_relat_1(X0),k2_relat_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.97      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_98]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_1723,plain,
% 3.87/0.97      ( r1_tarski(k2_relat_1(sK3),k2_relat_1(k2_zfmisc_1(sK0,sK2)))
% 3.87/0.97      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
% 3.87/0.97      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_712]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_9,plain,
% 3.87/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.87/0.97      inference(cnf_transformation,[],[f35]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_1162,plain,
% 3.87/0.97      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_162,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.87/0.97      inference(bin_hyper_res,[status(thm)],[c_8,c_137]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_681,plain,
% 3.87/0.97      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.87/0.97      | v1_relat_1(X0)
% 3.87/0.97      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_162]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_1085,plain,
% 3.87/0.97      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
% 3.87/0.97      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 3.87/0.97      | v1_relat_1(sK3) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_681]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_7,plain,
% 3.87/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.87/0.97      inference(cnf_transformation,[],[f32]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_134,plain,
% 3.87/0.97      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.87/0.97      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_135,plain,
% 3.87/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.87/0.97      inference(renaming,[status(thm)],[c_134]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_16,negated_conjecture,
% 3.87/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.87/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_234,plain,
% 3.87/0.97      ( r1_tarski(X0,X1)
% 3.87/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X1)
% 3.87/0.97      | sK3 != X0 ),
% 3.87/0.97      inference(resolution_lifted,[status(thm)],[c_135,c_16]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_235,plain,
% 3.87/0.97      ( r1_tarski(sK3,X0)
% 3.87/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(X0) ),
% 3.87/0.97      inference(unflattening,[status(thm)],[c_234]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_733,plain,
% 3.87/0.97      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
% 3.87/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_235]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_732,plain,
% 3.87/0.97      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)) ),
% 3.87/0.97      inference(instantiation,[status(thm)],[c_356]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(c_15,negated_conjecture,
% 3.87/0.97      ( r1_tarski(k1_relat_1(sK3),sK1) ),
% 3.87/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.87/0.97  
% 3.87/0.97  cnf(contradiction,plain,
% 3.87/0.97      ( $false ),
% 3.87/0.97      inference(minisat,
% 3.87/0.97                [status(thm)],
% 3.87/0.97                [c_15369,c_11456,c_7522,c_1723,c_1162,c_1085,c_733,c_732,
% 3.87/0.97                 c_15]) ).
% 3.87/0.97  
% 3.87/0.97  
% 3.87/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.97  
% 3.87/0.97  ------                               Statistics
% 3.87/0.97  
% 3.87/0.97  ------ Selected
% 3.87/0.97  
% 3.87/0.97  total_time:                             0.387
% 3.87/0.97  
%------------------------------------------------------------------------------
