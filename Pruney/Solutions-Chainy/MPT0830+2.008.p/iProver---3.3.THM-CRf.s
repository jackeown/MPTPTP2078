%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:27 EST 2020

% Result     : Theorem 23.86s
% Output     : CNFRefutation 23.86s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 662 expanded)
%              Number of clauses        :  110 ( 258 expanded)
%              Number of leaves         :   19 ( 140 expanded)
%              Depth                    :   18
%              Number of atoms          :  365 (1496 expanded)
%              Number of equality atoms :  102 ( 240 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f30])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_269,plain,
    ( X0 != X1
    | k7_relat_1(X2,X0) = k7_relat_1(X2,X1) ),
    theory(equality)).

cnf(c_263,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_936,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_263,c_272])).

cnf(c_2918,plain,
    ( ~ m1_subset_1(k7_relat_1(X0,X1),X2)
    | m1_subset_1(k7_relat_1(X0,X3),X2)
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_269,c_936])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1326,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(resolution,[status(thm)],[c_13,c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1926,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(k1_relat_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_1326,c_12])).

cnf(c_39122,plain,
    ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
    | ~ r1_tarski(k7_relat_1(X0,X3),sK3)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X0,X3)),X2)
    | X1 != X3 ),
    inference(resolution,[status(thm)],[c_2918,c_1926])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_40943,plain,
    ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
    | ~ v4_relat_1(k7_relat_1(X0,X3),X2)
    | ~ r1_tarski(k7_relat_1(X0,X3),sK3)
    | ~ v1_relat_1(k7_relat_1(X0,X3))
    | X1 != X3 ),
    inference(resolution,[status(thm)],[c_39122,c_3])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1923,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_1326,c_9])).

cnf(c_97800,plain,
    ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
    | ~ v4_relat_1(k7_relat_1(X0,X3),X2)
    | ~ r1_tarski(k7_relat_1(X0,X3),sK3)
    | X1 != X3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_40943,c_1923])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_665,plain,
    ( v4_relat_1(sK3,sK0) ),
    inference(resolution,[status(thm)],[c_10,c_15])).

cnf(c_1823,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_5,c_665])).

cnf(c_617,plain,
    ( v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_9,c_15])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | v4_relat_1(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_712,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_925,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0)
    | ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_2105,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1823,c_15,c_617,c_641,c_925])).

cnf(c_97826,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ r1_tarski(k7_relat_1(sK3,X1),sK3)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_97800,c_2105])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_714,plain,
    ( ~ v4_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_897,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1111,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,X0),X1)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1)
    | ~ v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_267,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2919,plain,
    ( ~ v4_relat_1(k7_relat_1(X0,X1),X2)
    | v4_relat_1(k7_relat_1(X0,X3),X2)
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_269,c_267])).

cnf(c_7039,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X1)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_2919,c_2105])).

cnf(c_39117,plain,
    ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k7_relat_1(X0,X2),sK3)
    | X1 != X2 ),
    inference(resolution,[status(thm)],[c_2918,c_1326])).

cnf(c_266,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3110,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_266,c_263])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5394,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k7_relat_1(X0,X1),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_3110,c_8])).

cnf(c_39525,plain,
    ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v4_relat_1(X0,X2)
    | ~ r1_tarski(X0,sK3)
    | ~ v1_relat_1(X0)
    | X1 != X2 ),
    inference(resolution,[status(thm)],[c_39117,c_5394])).

cnf(c_573,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_575,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_755,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_575])).

cnf(c_579,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1296,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_755,c_579])).

cnf(c_1307,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_relat_1(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1296])).

cnf(c_40845,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ v4_relat_1(X0,X2)
    | m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | X1 != X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_39525,c_1307])).

cnf(c_40846,plain,
    ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v4_relat_1(X0,X2)
    | ~ r1_tarski(X0,sK3)
    | X1 != X2 ),
    inference(renaming,[status(thm)],[c_40845])).

cnf(c_264,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2942,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_264,c_263])).

cnf(c_4451,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | X0 = k7_relat_1(X0,X1) ),
    inference(resolution,[status(thm)],[c_2942,c_8])).

cnf(c_40921,plain,
    ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v4_relat_1(X1,X2)
    | ~ v4_relat_1(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(X0,sK3)
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_40846,c_4451])).

cnf(c_3102,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X3,k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_266,c_8])).

cnf(c_12881,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_3102,c_263])).

cnf(c_1424,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ r1_tarski(k1_relat_1(sK3),X0) ),
    inference(resolution,[status(thm)],[c_12,c_15])).

cnf(c_1433,plain,
    ( v4_relat_1(sK3,X0)
    | ~ r1_tarski(k1_relat_1(sK3),X0) ),
    inference(resolution,[status(thm)],[c_1424,c_10])).

cnf(c_42298,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(sK3,k7_relat_1(X0,X1))
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12881,c_1433])).

cnf(c_46427,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(sK3,sK3)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_40921,c_42298])).

cnf(c_1,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_587,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1000,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_576])).

cnf(c_578,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v4_relat_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1909,plain,
    ( v4_relat_1(sK3,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_578])).

cnf(c_3049,plain,
    ( v4_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_1909])).

cnf(c_580,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3231,plain,
    ( k7_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_580])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(X0),X3),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k2_xboole_0(k1_relat_1(X0),X3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_799,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(sK3),X0),sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(sK3),k2_xboole_0(k1_relat_1(sK3),X0)) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_821,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(sK3),X0),sK2)))
    | v4_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_671,plain,
    ( r1_tarski(k1_relat_1(X0),k2_xboole_0(k1_relat_1(X0),X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_889,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_xboole_0(k1_relat_1(sK3),X0)) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_711,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1156,plain,
    ( ~ v4_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0))
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) = sK3 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_3963,plain,
    ( k7_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3231,c_15,c_617,c_799,c_821,c_889,c_1156])).

cnf(c_850,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_578])).

cnf(c_1544,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_580])).

cnf(c_894,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK0) = sK3 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1798,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1544,c_15,c_617,c_641,c_894])).

cnf(c_847,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_579])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_581,plain,
    ( k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1539,plain,
    ( k2_xboole_0(k7_relat_1(sK3,X0),k7_relat_1(sK3,X1)) = k7_relat_1(sK3,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_847,c_581])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2079,plain,
    ( k2_xboole_0(k7_relat_1(sK3,X0),k7_relat_1(sK3,X1)) = k7_relat_1(sK3,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1539,c_0])).

cnf(c_2309,plain,
    ( k7_relat_1(sK3,k2_xboole_0(X0,sK0)) = k2_xboole_0(sK3,k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1798,c_2079])).

cnf(c_685,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_587])).

cnf(c_2078,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k7_relat_1(sK3,k2_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_685])).

cnf(c_2628,plain,
    ( r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),k7_relat_1(sK3,k2_xboole_0(X1,k2_xboole_0(X0,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_2078])).

cnf(c_13227,plain,
    ( r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3963,c_2628])).

cnf(c_13282,plain,
    ( r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13227])).

cnf(c_2076,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k7_relat_1(sK3,k2_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_587])).

cnf(c_2635,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_xboole_0(sK3,k7_relat_1(sK3,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_2076])).

cnf(c_1297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_755,c_575])).

cnf(c_19098,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2635,c_1297])).

cnf(c_19105,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19098])).

cnf(c_46850,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46427,c_13282,c_19105])).

cnf(c_47286,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) ),
    inference(resolution,[status(thm)],[c_46850,c_12])).

cnf(c_98300,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | X0 != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_97826,c_15,c_617,c_641,c_897,c_1111,c_7039,c_47286])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k5_relset_1(X1,X2,X0,X3),X4)
    | ~ m1_subset_1(k7_relat_1(X0,X3),X4) ),
    inference(resolution,[status(thm)],[c_936,c_11])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_50850,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[status(thm)],[c_1044,c_14])).

cnf(c_577,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_932,plain,
    ( k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_573,c_577])).

cnf(c_574,plain,
    ( m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1686,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_574])).

cnf(c_1687,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1686])).

cnf(c_51125,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_50850,c_1687])).

cnf(c_98333,plain,
    ( sK1 != sK1 ),
    inference(resolution,[status(thm)],[c_98300,c_51125])).

cnf(c_98334,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_98333])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:27:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.86/3.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.86/3.48  
% 23.86/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.86/3.48  
% 23.86/3.48  ------  iProver source info
% 23.86/3.48  
% 23.86/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.86/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.86/3.48  git: non_committed_changes: false
% 23.86/3.48  git: last_make_outside_of_git: false
% 23.86/3.48  
% 23.86/3.48  ------ 
% 23.86/3.48  ------ Parsing...
% 23.86/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.86/3.48  
% 23.86/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.86/3.48  
% 23.86/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.86/3.48  
% 23.86/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.86/3.48  ------ Proving...
% 23.86/3.48  ------ Problem Properties 
% 23.86/3.48  
% 23.86/3.48  
% 23.86/3.48  clauses                                 16
% 23.86/3.48  conjectures                             2
% 23.86/3.48  EPR                                     0
% 23.86/3.48  Horn                                    16
% 23.86/3.48  unary                                   4
% 23.86/3.48  binary                                  4
% 23.86/3.48  lits                                    36
% 23.86/3.48  lits eq                                 4
% 23.86/3.48  fd_pure                                 0
% 23.86/3.48  fd_pseudo                               0
% 23.86/3.48  fd_cond                                 0
% 23.86/3.48  fd_pseudo_cond                          0
% 23.86/3.48  AC symbols                              0
% 23.86/3.48  
% 23.86/3.48  ------ Input Options Time Limit: Unbounded
% 23.86/3.48  
% 23.86/3.48  
% 23.86/3.48  ------ 
% 23.86/3.48  Current options:
% 23.86/3.48  ------ 
% 23.86/3.48  
% 23.86/3.48  
% 23.86/3.48  
% 23.86/3.48  
% 23.86/3.48  ------ Proving...
% 23.86/3.48  
% 23.86/3.48  
% 23.86/3.48  % SZS status Theorem for theBenchmark.p
% 23.86/3.48  
% 23.86/3.48   Resolution empty clause
% 23.86/3.48  
% 23.86/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.86/3.48  
% 23.86/3.48  fof(f11,axiom,(
% 23.86/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f26,plain,(
% 23.86/3.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.86/3.48    inference(ennf_transformation,[],[f11])).
% 23.86/3.48  
% 23.86/3.48  fof(f27,plain,(
% 23.86/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.86/3.48    inference(flattening,[],[f26])).
% 23.86/3.48  
% 23.86/3.48  fof(f45,plain,(
% 23.86/3.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 23.86/3.48    inference(cnf_transformation,[],[f27])).
% 23.86/3.48  
% 23.86/3.48  fof(f12,conjecture,(
% 23.86/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f13,negated_conjecture,(
% 23.86/3.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.86/3.48    inference(negated_conjecture,[],[f12])).
% 23.86/3.48  
% 23.86/3.48  fof(f28,plain,(
% 23.86/3.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 23.86/3.48    inference(ennf_transformation,[],[f13])).
% 23.86/3.48  
% 23.86/3.48  fof(f30,plain,(
% 23.86/3.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 23.86/3.48    introduced(choice_axiom,[])).
% 23.86/3.48  
% 23.86/3.48  fof(f31,plain,(
% 23.86/3.48    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 23.86/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f30])).
% 23.86/3.48  
% 23.86/3.48  fof(f46,plain,(
% 23.86/3.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 23.86/3.48    inference(cnf_transformation,[],[f31])).
% 23.86/3.48  
% 23.86/3.48  fof(f10,axiom,(
% 23.86/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f24,plain,(
% 23.86/3.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 23.86/3.48    inference(ennf_transformation,[],[f10])).
% 23.86/3.48  
% 23.86/3.48  fof(f25,plain,(
% 23.86/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 23.86/3.48    inference(flattening,[],[f24])).
% 23.86/3.48  
% 23.86/3.48  fof(f44,plain,(
% 23.86/3.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 23.86/3.48    inference(cnf_transformation,[],[f25])).
% 23.86/3.48  
% 23.86/3.48  fof(f3,axiom,(
% 23.86/3.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f15,plain,(
% 23.86/3.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.86/3.48    inference(ennf_transformation,[],[f3])).
% 23.86/3.48  
% 23.86/3.48  fof(f29,plain,(
% 23.86/3.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 23.86/3.48    inference(nnf_transformation,[],[f15])).
% 23.86/3.48  
% 23.86/3.48  fof(f34,plain,(
% 23.86/3.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.86/3.48    inference(cnf_transformation,[],[f29])).
% 23.86/3.48  
% 23.86/3.48  fof(f7,axiom,(
% 23.86/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f21,plain,(
% 23.86/3.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.86/3.48    inference(ennf_transformation,[],[f7])).
% 23.86/3.48  
% 23.86/3.48  fof(f41,plain,(
% 23.86/3.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.86/3.48    inference(cnf_transformation,[],[f21])).
% 23.86/3.48  
% 23.86/3.48  fof(f4,axiom,(
% 23.86/3.48    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f16,plain,(
% 23.86/3.48    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 23.86/3.48    inference(ennf_transformation,[],[f4])).
% 23.86/3.48  
% 23.86/3.48  fof(f17,plain,(
% 23.86/3.48    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 23.86/3.48    inference(flattening,[],[f16])).
% 23.86/3.48  
% 23.86/3.48  fof(f37,plain,(
% 23.86/3.48    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 23.86/3.48    inference(cnf_transformation,[],[f17])).
% 23.86/3.48  
% 23.86/3.48  fof(f8,axiom,(
% 23.86/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f14,plain,(
% 23.86/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 23.86/3.48    inference(pure_predicate_removal,[],[f8])).
% 23.86/3.48  
% 23.86/3.48  fof(f22,plain,(
% 23.86/3.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.86/3.48    inference(ennf_transformation,[],[f14])).
% 23.86/3.48  
% 23.86/3.48  fof(f42,plain,(
% 23.86/3.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.86/3.48    inference(cnf_transformation,[],[f22])).
% 23.86/3.48  
% 23.86/3.48  fof(f36,plain,(
% 23.86/3.48    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 23.86/3.48    inference(cnf_transformation,[],[f17])).
% 23.86/3.48  
% 23.86/3.48  fof(f6,axiom,(
% 23.86/3.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f19,plain,(
% 23.86/3.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 23.86/3.48    inference(ennf_transformation,[],[f6])).
% 23.86/3.48  
% 23.86/3.48  fof(f20,plain,(
% 23.86/3.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.86/3.48    inference(flattening,[],[f19])).
% 23.86/3.48  
% 23.86/3.48  fof(f40,plain,(
% 23.86/3.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.86/3.48    inference(cnf_transformation,[],[f20])).
% 23.86/3.48  
% 23.86/3.48  fof(f2,axiom,(
% 23.86/3.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f33,plain,(
% 23.86/3.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 23.86/3.48    inference(cnf_transformation,[],[f2])).
% 23.86/3.48  
% 23.86/3.48  fof(f5,axiom,(
% 23.86/3.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f18,plain,(
% 23.86/3.48    ! [X0,X1,X2] : (k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 23.86/3.48    inference(ennf_transformation,[],[f5])).
% 23.86/3.48  
% 23.86/3.48  fof(f39,plain,(
% 23.86/3.48    ( ! [X2,X0,X1] : (k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 23.86/3.48    inference(cnf_transformation,[],[f18])).
% 23.86/3.48  
% 23.86/3.48  fof(f1,axiom,(
% 23.86/3.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f32,plain,(
% 23.86/3.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.86/3.48    inference(cnf_transformation,[],[f1])).
% 23.86/3.48  
% 23.86/3.48  fof(f9,axiom,(
% 23.86/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 23.86/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.86/3.48  
% 23.86/3.48  fof(f23,plain,(
% 23.86/3.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.86/3.48    inference(ennf_transformation,[],[f9])).
% 23.86/3.48  
% 23.86/3.48  fof(f43,plain,(
% 23.86/3.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.86/3.48    inference(cnf_transformation,[],[f23])).
% 23.86/3.48  
% 23.86/3.48  fof(f47,plain,(
% 23.86/3.48    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 23.86/3.48    inference(cnf_transformation,[],[f31])).
% 23.86/3.48  
% 23.86/3.48  cnf(c_269,plain,
% 23.86/3.48      ( X0 != X1 | k7_relat_1(X2,X0) = k7_relat_1(X2,X1) ),
% 23.86/3.48      theory(equality) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_263,plain,( X0 = X0 ),theory(equality) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_272,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.86/3.48      theory(equality) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_936,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_263,c_272]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2918,plain,
% 23.86/3.48      ( ~ m1_subset_1(k7_relat_1(X0,X1),X2)
% 23.86/3.48      | m1_subset_1(k7_relat_1(X0,X3),X2)
% 23.86/3.48      | X3 != X1 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_269,c_936]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_13,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.86/3.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.86/3.48      | ~ r1_tarski(X3,X0) ),
% 23.86/3.48      inference(cnf_transformation,[],[f45]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_15,negated_conjecture,
% 23.86/3.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 23.86/3.48      inference(cnf_transformation,[],[f46]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1326,plain,
% 23.86/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | ~ r1_tarski(X0,sK3) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_13,c_15]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_12,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.86/3.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 23.86/3.48      inference(cnf_transformation,[],[f44]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1926,plain,
% 23.86/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 23.86/3.48      | ~ r1_tarski(X0,sK3)
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(X0),X1) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_1326,c_12]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_39122,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
% 23.86/3.48      | ~ r1_tarski(k7_relat_1(X0,X3),sK3)
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(k7_relat_1(X0,X3)),X2)
% 23.86/3.48      | X1 != X3 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_2918,c_1926]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_3,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 23.86/3.48      inference(cnf_transformation,[],[f34]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_40943,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
% 23.86/3.48      | ~ v4_relat_1(k7_relat_1(X0,X3),X2)
% 23.86/3.48      | ~ r1_tarski(k7_relat_1(X0,X3),sK3)
% 23.86/3.48      | ~ v1_relat_1(k7_relat_1(X0,X3))
% 23.86/3.48      | X1 != X3 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_39122,c_3]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_9,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 23.86/3.48      inference(cnf_transformation,[],[f41]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1923,plain,
% 23.86/3.48      ( ~ r1_tarski(X0,sK3) | v1_relat_1(X0) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_1326,c_9]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_97800,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
% 23.86/3.48      | ~ v4_relat_1(k7_relat_1(X0,X3),X2)
% 23.86/3.48      | ~ r1_tarski(k7_relat_1(X0,X3),sK3)
% 23.86/3.48      | X1 != X3 ),
% 23.86/3.48      inference(forward_subsumption_resolution,[status(thm)],[c_40943,c_1923]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_5,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1)
% 23.86/3.48      | v4_relat_1(k7_relat_1(X0,X2),X2)
% 23.86/3.48      | ~ v1_relat_1(X0) ),
% 23.86/3.48      inference(cnf_transformation,[],[f37]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_10,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 23.86/3.48      inference(cnf_transformation,[],[f42]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_665,plain,
% 23.86/3.48      ( v4_relat_1(sK3,sK0) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_10,c_15]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1823,plain,
% 23.86/3.48      ( v4_relat_1(k7_relat_1(sK3,X0),X0) | ~ v1_relat_1(sK3) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_5,c_665]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_617,plain,
% 23.86/3.48      ( v1_relat_1(sK3) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_9,c_15]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_641,plain,
% 23.86/3.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | v4_relat_1(sK3,sK0) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_10]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_712,plain,
% 23.86/3.48      ( v4_relat_1(k7_relat_1(sK3,X0),X0)
% 23.86/3.48      | ~ v4_relat_1(sK3,X1)
% 23.86/3.48      | ~ v1_relat_1(sK3) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_5]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_925,plain,
% 23.86/3.48      ( v4_relat_1(k7_relat_1(sK3,X0),X0)
% 23.86/3.48      | ~ v4_relat_1(sK3,sK0)
% 23.86/3.48      | ~ v1_relat_1(sK3) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_712]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2105,plain,
% 23.86/3.48      ( v4_relat_1(k7_relat_1(sK3,X0),X0) ),
% 23.86/3.48      inference(global_propositional_subsumption,
% 23.86/3.48                [status(thm)],
% 23.86/3.48                [c_1823,c_15,c_617,c_641,c_925]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_97826,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 23.86/3.48      | ~ r1_tarski(k7_relat_1(sK3,X1),sK3)
% 23.86/3.48      | X0 != X1 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_97800,c_2105]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_6,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1)
% 23.86/3.48      | ~ v1_relat_1(X0)
% 23.86/3.48      | v1_relat_1(k7_relat_1(X0,X2)) ),
% 23.86/3.48      inference(cnf_transformation,[],[f36]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_714,plain,
% 23.86/3.48      ( ~ v4_relat_1(sK3,X0)
% 23.86/3.48      | v1_relat_1(k7_relat_1(sK3,X1))
% 23.86/3.48      | ~ v1_relat_1(sK3) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_6]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_897,plain,
% 23.86/3.48      ( ~ v4_relat_1(sK3,sK0)
% 23.86/3.48      | v1_relat_1(k7_relat_1(sK3,X0))
% 23.86/3.48      | ~ v1_relat_1(sK3) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_714]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1111,plain,
% 23.86/3.48      ( ~ v4_relat_1(k7_relat_1(sK3,X0),X1)
% 23.86/3.48      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1)
% 23.86/3.48      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_3]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_267,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1) | v4_relat_1(X2,X1) | X2 != X0 ),
% 23.86/3.48      theory(equality) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2919,plain,
% 23.86/3.48      ( ~ v4_relat_1(k7_relat_1(X0,X1),X2)
% 23.86/3.48      | v4_relat_1(k7_relat_1(X0,X3),X2)
% 23.86/3.48      | X3 != X1 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_269,c_267]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_7039,plain,
% 23.86/3.48      ( v4_relat_1(k7_relat_1(sK3,X0),X1) | X0 != X1 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_2919,c_2105]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_39117,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | ~ r1_tarski(k7_relat_1(X0,X2),sK3)
% 23.86/3.48      | X1 != X2 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_2918,c_1326]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_266,plain,
% 23.86/3.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.86/3.48      theory(equality) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_3110,plain,
% 23.86/3.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_266,c_263]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_8,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 23.86/3.48      inference(cnf_transformation,[],[f40]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_5394,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1)
% 23.86/3.48      | ~ r1_tarski(X0,X2)
% 23.86/3.48      | r1_tarski(k7_relat_1(X0,X1),X2)
% 23.86/3.48      | ~ v1_relat_1(X0) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_3110,c_8]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_39525,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | ~ v4_relat_1(X0,X2)
% 23.86/3.48      | ~ r1_tarski(X0,sK3)
% 23.86/3.48      | ~ v1_relat_1(X0)
% 23.86/3.48      | X1 != X2 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_39117,c_5394]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_573,plain,
% 23.86/3.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_575,plain,
% 23.86/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.86/3.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 23.86/3.48      | r1_tarski(X3,X0) != iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_755,plain,
% 23.86/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 23.86/3.48      | r1_tarski(X0,sK3) != iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_573,c_575]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_579,plain,
% 23.86/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.86/3.48      | v1_relat_1(X0) = iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1296,plain,
% 23.86/3.48      ( r1_tarski(X0,sK3) != iProver_top | v1_relat_1(X0) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_755,c_579]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1307,plain,
% 23.86/3.48      ( ~ r1_tarski(X0,sK3) | v1_relat_1(X0) ),
% 23.86/3.48      inference(predicate_to_equality_rev,[status(thm)],[c_1296]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_40845,plain,
% 23.86/3.48      ( ~ r1_tarski(X0,sK3)
% 23.86/3.48      | ~ v4_relat_1(X0,X2)
% 23.86/3.48      | m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | X1 != X2 ),
% 23.86/3.48      inference(global_propositional_subsumption,
% 23.86/3.48                [status(thm)],
% 23.86/3.48                [c_39525,c_1307]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_40846,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | ~ v4_relat_1(X0,X2)
% 23.86/3.48      | ~ r1_tarski(X0,sK3)
% 23.86/3.48      | X1 != X2 ),
% 23.86/3.48      inference(renaming,[status(thm)],[c_40845]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_264,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2942,plain,
% 23.86/3.48      ( X0 != X1 | X1 = X0 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_264,c_263]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_4451,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | X0 = k7_relat_1(X0,X1) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_2942,c_8]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_40921,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | ~ v4_relat_1(X1,X2)
% 23.86/3.48      | ~ v4_relat_1(X0,k7_relat_1(X1,X2))
% 23.86/3.48      | ~ r1_tarski(X0,sK3)
% 23.86/3.48      | ~ v1_relat_1(X1) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_40846,c_4451]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_3102,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1)
% 23.86/3.48      | ~ r1_tarski(X2,X0)
% 23.86/3.48      | r1_tarski(X3,k7_relat_1(X0,X1))
% 23.86/3.48      | ~ v1_relat_1(X0)
% 23.86/3.48      | X3 != X2 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_266,c_8]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_12881,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1)
% 23.86/3.48      | ~ r1_tarski(X2,X0)
% 23.86/3.48      | r1_tarski(X2,k7_relat_1(X0,X1))
% 23.86/3.48      | ~ v1_relat_1(X0) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_3102,c_263]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1424,plain,
% 23.86/3.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(sK3),X0) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_12,c_15]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1433,plain,
% 23.86/3.48      ( v4_relat_1(sK3,X0) | ~ r1_tarski(k1_relat_1(sK3),X0) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_1424,c_10]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_42298,plain,
% 23.86/3.48      ( ~ v4_relat_1(X0,X1)
% 23.86/3.48      | v4_relat_1(sK3,k7_relat_1(X0,X1))
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 23.86/3.48      | ~ v1_relat_1(X0) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_12881,c_1433]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_46427,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | ~ v4_relat_1(X0,X1)
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 23.86/3.48      | ~ r1_tarski(sK3,sK3)
% 23.86/3.48      | ~ v1_relat_1(X0) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_40921,c_42298]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1,plain,
% 23.86/3.48      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 23.86/3.48      inference(cnf_transformation,[],[f33]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_587,plain,
% 23.86/3.48      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_576,plain,
% 23.86/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.86/3.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 23.86/3.48      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1000,plain,
% 23.86/3.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) = iProver_top
% 23.86/3.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_573,c_576]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_578,plain,
% 23.86/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.86/3.48      | v4_relat_1(X0,X1) = iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1909,plain,
% 23.86/3.48      ( v4_relat_1(sK3,X0) = iProver_top
% 23.86/3.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_1000,c_578]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_3049,plain,
% 23.86/3.48      ( v4_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_587,c_1909]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_580,plain,
% 23.86/3.48      ( k7_relat_1(X0,X1) = X0
% 23.86/3.48      | v4_relat_1(X0,X1) != iProver_top
% 23.86/3.48      | v1_relat_1(X0) != iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_3231,plain,
% 23.86/3.48      ( k7_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) = sK3
% 23.86/3.48      | v1_relat_1(sK3) != iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_3049,c_580]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_672,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.86/3.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(X0),X3),X2)))
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(X0),k2_xboole_0(k1_relat_1(X0),X3)) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_12]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_799,plain,
% 23.86/3.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(sK3),X0),sK2)))
% 23.86/3.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(sK3),k2_xboole_0(k1_relat_1(sK3),X0)) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_672]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_821,plain,
% 23.86/3.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_relat_1(sK3),X0),sK2)))
% 23.86/3.48      | v4_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_10]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_671,plain,
% 23.86/3.48      ( r1_tarski(k1_relat_1(X0),k2_xboole_0(k1_relat_1(X0),X1)) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_1]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_889,plain,
% 23.86/3.48      ( r1_tarski(k1_relat_1(sK3),k2_xboole_0(k1_relat_1(sK3),X0)) ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_671]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_711,plain,
% 23.86/3.48      ( ~ v4_relat_1(sK3,X0) | ~ v1_relat_1(sK3) | k7_relat_1(sK3,X0) = sK3 ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_8]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1156,plain,
% 23.86/3.48      ( ~ v4_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0))
% 23.86/3.48      | ~ v1_relat_1(sK3)
% 23.86/3.48      | k7_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) = sK3 ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_711]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_3963,plain,
% 23.86/3.48      ( k7_relat_1(sK3,k2_xboole_0(k1_relat_1(sK3),X0)) = sK3 ),
% 23.86/3.48      inference(global_propositional_subsumption,
% 23.86/3.48                [status(thm)],
% 23.86/3.48                [c_3231,c_15,c_617,c_799,c_821,c_889,c_1156]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_850,plain,
% 23.86/3.48      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_573,c_578]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1544,plain,
% 23.86/3.48      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_850,c_580]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_894,plain,
% 23.86/3.48      ( ~ v4_relat_1(sK3,sK0) | ~ v1_relat_1(sK3) | k7_relat_1(sK3,sK0) = sK3 ),
% 23.86/3.48      inference(instantiation,[status(thm)],[c_711]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1798,plain,
% 23.86/3.48      ( k7_relat_1(sK3,sK0) = sK3 ),
% 23.86/3.48      inference(global_propositional_subsumption,
% 23.86/3.48                [status(thm)],
% 23.86/3.48                [c_1544,c_15,c_617,c_641,c_894]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_847,plain,
% 23.86/3.48      ( v1_relat_1(sK3) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_573,c_579]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_7,plain,
% 23.86/3.48      ( ~ v1_relat_1(X0)
% 23.86/3.48      | k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 23.86/3.48      inference(cnf_transformation,[],[f39]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_581,plain,
% 23.86/3.48      ( k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2))
% 23.86/3.48      | v1_relat_1(X0) != iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1539,plain,
% 23.86/3.48      ( k2_xboole_0(k7_relat_1(sK3,X0),k7_relat_1(sK3,X1)) = k7_relat_1(sK3,k2_xboole_0(X0,X1)) ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_847,c_581]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_0,plain,
% 23.86/3.48      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 23.86/3.48      inference(cnf_transformation,[],[f32]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2079,plain,
% 23.86/3.48      ( k2_xboole_0(k7_relat_1(sK3,X0),k7_relat_1(sK3,X1)) = k7_relat_1(sK3,k2_xboole_0(X1,X0)) ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_1539,c_0]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2309,plain,
% 23.86/3.48      ( k7_relat_1(sK3,k2_xboole_0(X0,sK0)) = k2_xboole_0(sK3,k7_relat_1(sK3,X0)) ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_1798,c_2079]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_685,plain,
% 23.86/3.48      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_0,c_587]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2078,plain,
% 23.86/3.48      ( r1_tarski(k7_relat_1(sK3,X0),k7_relat_1(sK3,k2_xboole_0(X1,X0))) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_1539,c_685]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2628,plain,
% 23.86/3.48      ( r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),k7_relat_1(sK3,k2_xboole_0(X1,k2_xboole_0(X0,sK0)))) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_2309,c_2078]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_13227,plain,
% 23.86/3.48      ( r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),sK3) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_3963,c_2628]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_13282,plain,
% 23.86/3.48      ( r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),sK3) ),
% 23.86/3.48      inference(predicate_to_equality_rev,[status(thm)],[c_13227]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2076,plain,
% 23.86/3.48      ( r1_tarski(k7_relat_1(sK3,X0),k7_relat_1(sK3,k2_xboole_0(X0,X1))) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_1539,c_587]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_2635,plain,
% 23.86/3.48      ( r1_tarski(k7_relat_1(sK3,X0),k2_xboole_0(sK3,k7_relat_1(sK3,X0))) = iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_2309,c_2076]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1297,plain,
% 23.86/3.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 23.86/3.48      | r1_tarski(X0,X1) != iProver_top
% 23.86/3.48      | r1_tarski(X1,sK3) != iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_755,c_575]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_19098,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 23.86/3.48      | r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),sK3) != iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_2635,c_1297]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_19105,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 23.86/3.48      | ~ r1_tarski(k2_xboole_0(sK3,k7_relat_1(sK3,X0)),sK3) ),
% 23.86/3.48      inference(predicate_to_equality_rev,[status(thm)],[c_19098]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_46850,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 23.86/3.48      inference(global_propositional_subsumption,
% 23.86/3.48                [status(thm)],
% 23.86/3.48                [c_46427,c_13282,c_19105]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_47286,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 23.86/3.48      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_46850,c_12]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_98300,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 23.86/3.48      | X0 != X1 ),
% 23.86/3.48      inference(global_propositional_subsumption,
% 23.86/3.48                [status(thm)],
% 23.86/3.48                [c_97826,c_15,c_617,c_641,c_897,c_1111,c_7039,c_47286]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_11,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.86/3.48      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 23.86/3.48      inference(cnf_transformation,[],[f43]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1044,plain,
% 23.86/3.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.86/3.48      | m1_subset_1(k5_relset_1(X1,X2,X0,X3),X4)
% 23.86/3.48      | ~ m1_subset_1(k7_relat_1(X0,X3),X4) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_936,c_11]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_14,negated_conjecture,
% 23.86/3.48      ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 23.86/3.48      inference(cnf_transformation,[],[f47]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_50850,plain,
% 23.86/3.48      ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 23.86/3.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_1044,c_14]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_577,plain,
% 23.86/3.48      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 23.86/3.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_932,plain,
% 23.86/3.48      ( k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_573,c_577]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_574,plain,
% 23.86/3.48      ( m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 23.86/3.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1686,plain,
% 23.86/3.48      ( m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 23.86/3.48      inference(superposition,[status(thm)],[c_932,c_574]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_1687,plain,
% 23.86/3.48      ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 23.86/3.48      inference(predicate_to_equality_rev,[status(thm)],[c_1686]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_51125,plain,
% 23.86/3.48      ( ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 23.86/3.48      inference(global_propositional_subsumption,
% 23.86/3.48                [status(thm)],
% 23.86/3.48                [c_50850,c_1687]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_98333,plain,
% 23.86/3.48      ( sK1 != sK1 ),
% 23.86/3.48      inference(resolution,[status(thm)],[c_98300,c_51125]) ).
% 23.86/3.48  
% 23.86/3.48  cnf(c_98334,plain,
% 23.86/3.48      ( $false ),
% 23.86/3.48      inference(equality_resolution_simp,[status(thm)],[c_98333]) ).
% 23.86/3.48  
% 23.86/3.48  
% 23.86/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.86/3.48  
% 23.86/3.48  ------                               Statistics
% 23.86/3.48  
% 23.86/3.48  ------ Selected
% 23.86/3.48  
% 23.86/3.48  total_time:                             2.757
% 23.86/3.48  
%------------------------------------------------------------------------------
